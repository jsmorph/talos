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
absolute value at most one.  The rational ties-to-even contract and its f32
division lift are also complete: for a nonzero finite denominator and a
quotient of magnitude at most one, the real error is at most `2^-23`, including
through gradual underflow.  The square-root contract is complete as well: on
positive finite inputs at most one, both the operation and decoded WAT program
are within `2^-23` of the exact real square root.  Finally, the cubic sine
example has a combined analytic-plus-roundoff theorem on `|x| ≤ 1/2`.  All
strengthening units are complete and pushed independently.

### Current execution status (2026-09-02)

1. **Complete and pushed:** proof-visible f64 integer conversions and example
   program theorems (`8a4f27f` remote checkpoint).
2. **Complete and pushed:** replacement of all five IEEE32 compatibility
   axioms by proofs (`f45b4b4` remote checkpoint).
3. **Complete and pushed:** exact dyadic rounding plus the f32 multiplication
   `2^-23` real-error theorem (`45a7383` remote checkpoint).
4. **Complete and pushed:** exact rational ties-to-even rounding plus f32
   division and decoded-WAT `2^-23` real-error theorems (`8d5234c` remote
   checkpoint).
5. **Complete and pushed:** exact square-root midpoint rounding, packing
   through the verified scaled-magnitude rounder, and operation/WAT real error
   bounds of `2^-23` for positive finite inputs at most one.  The interpreter
   square-root examples and regression suite and the CodeLib theorem root pass
   under Lean 4.34.0-rc2, with only standard logical axioms reported
   (`9f32c23` remote checkpoint).
6. **Complete and pushed:** reusable addition/subtraction real-error
   contracts and the cubic sine theorem on `|x| ≤ 1/2`.  The proof combines a
   `1/3200` real approximation bound with a conservative `3 * 2^-23` primitive
   roundoff budget, proving both the operation result and decoded WAT program
   stay strictly within `2^-11` of `Real.sin` (`465aef5` remote checkpoint).
7. **Complete:** all affected interpreter and CodeLib roots build with exact
   Lean 4.34.0-rc2.  Public theorem axiom reports and `git diff --check` pass.
   The compatibility declarations are now theorems with no axiom dependencies,
   and every new general numerical theorem is free of `sorryAx`, native-oracle
   axioms, and floating-point bridge axioms.

## Quantitative kernel execution agenda (2026-09-02)

The next work proceeds in this fixed order, with a passing commit pushed after
each phase:

1. **Quantitative f64 arithmetic.**  Prove finite real-error results for
   binary64 addition, subtraction, multiplication, division, and square root
   under explicit bounded-domain hypotheses.  Add fuel-independent decoded-WAT
   theorems for representative operations and retain the native IEEE64 suite as
   a regression oracle.
2. **Reusable error composition.**  Add lemmas for perturbation sums,
   perturbed products, division by exact nonzero constants, and sequential
   Horner evaluation.  Refactor at least one existing numerical proof to use
   these results, so the interface is tested by a concrete consumer.
3. **Representative numerical kernels.**  Add hand-written decoded WAT and
   fuel-independent theorems for f32 and f64 affine or Horner evaluation and a
   dot-product kernel.  State finite-result, accumulated-error, and overflow-
   exclusion hypotheses explicitly.
4. **Final validation.**  Build the affected interpreter and CodeLib roots
   with Lean 4.34.0-rc2, inspect public theorem axiom reports, scan the changed
   sources, update this plan and `journal.md`, and push the final tree.

### Current status

Phase 1 is complete.  Binary64 addition, subtraction, multiplication,
division, and square root have finite `2^-52` real-error results on their
explicit bounded domains.  Each operation is represented by decoded
hand-written WAT with an explicit small-step trace and a fuel-independent
execution/error theorem.  Phase 2 is complete: the format-independent error
composition module covers sums, products, exact-constant division, and
sequential Horner evaluation, and the f32 cubic sine proof consumes the new
interface without changing its public result.  Phase 3 is complete: decoded
f32 affine and two-term f64 dot-product kernels
have explicit traces, fuel-independent execution theorems, finite results, and
accumulated absolute error bounds under explicit operand and intermediate
magnitude assumptions.  Final combined validation remains in Phase 4.

All four phases are complete.  The combined interpreter and CodeLib target
sets pass with exact Lean 4.34.0-rc2; every new general theorem reports only
standard Lean logical axioms; the complete changed-source scan and Git
whitespace check pass; and every substantive checkpoint has been published
and fetch-verified against its local Git tree.

## Scalable numerical-kernel agenda (2026-09-02)

The next development turns the fixed affine and two-term dot-product examples
into consumers of reusable sequential-kernel theorems.  Work proceeds in four
independently validated and published checkpoints:

1. **List error algebra.**  Prove list-sum perturbation, sequential
   accumulation, general Horner recurrence, its weighted closed form, and the
   `|x| ≤ 1` corollary.  Refactor the existing two-step Horner lemma to use the
   general result.
2. **Generic modeled kernels.**  Define pure IEEE32 Horner and nonempty IEEE64
   dot-product folds with exact real counterparts and explicit recursive
   safety predicates.  Prove finiteness and accumulated-error results, then
   make the current affine and dot-two theorems corollaries where practical.
3. **Larger decoded-WAT consumers.**  Add a degree-three f32 Horner program and
   a four-term f64 dot product with decoder checks, explicit small-step traces,
   fuel-independent termination, and generic finite/error conclusions.
4. **Safety corollaries and final validation.**  Add useful sufficient
   conditions that discharge the explicit intermediate bounds without hiding
   them.  Rebuild every affected interpreter and CodeLib root, inspect public
   theorem axioms, scan all changed sources, update the plan and journal, and
   verify the final fetched remote tree.

Arbitrary-memory WAT loops remain a later extension.  The first scalable layer
uses unrolled decoded programs so that numerical induction and control-flow
invariants remain separate review units.

### Current scalable-kernel status

Checkpoint 1 is complete.  The error-composition layer now includes list-sum
and sequential perturbation theorems, explicit approximate Horner traces,
recursive and weighted closed-form error budgets, and the `|x| ≤ 1`
corollary.  The original two-step Horner theorem is derived from this general
recurrence.  Checkpoint 2 is complete: modeled IEEE32 Horner and nonempty
IEEE64 dot-product folds now have exact real counterparts, recursive safety
predicates, finiteness results, and accumulated-error theorems.  The fixed
affine and two-term dot-product results are derived from the generic folds.
Checkpoint 3 is complete: decoded unrolled WAT consumers cover a three-stage
f32 Horner evaluation and a four-term f64 dot product, with explicit traces,
fuel-independent termination, and error bounds supplied by the generic
folds.  Checkpoint 4's safety layer is complete: exact-real headroom predicates
now imply the explicit recursive safety conditions and feed both generic and
WAT theorems.  All four checkpoints are complete.  The combined interpreter
and CodeLib builds pass with exact Lean 4.34.0-rc2; every new general theorem
reports only standard logical axioms; the agenda-wide proof-hole and Git
whitespace scans pass; and every substantive tree has been published and
fetch-verified.

## Runtime memory-backed f64 dot-product flagship (2026-09-02)

The next milestone closes the arbitrary-memory-loop gap left by the scalable
kernel agenda.  Its flagship result is a fuel-independent correctness and
roundoff theorem for a runtime-length binary64 dot product over two read-only
arrays in WebAssembly linear memory.  The final public theorem must connect
the exact emitted WAT artifact to the existing pure IEEE64 list fold, prove
termination and memory preservation, establish a finite result, and bound its
distance from the exact real dot product.

For a nonempty input of length `n`, the target implementation initializes the
accumulator with the first rounded product and then performs `n - 1`
multiply-add stages using separate `f64.mul` and `f64.add` instructions.  This
matches the existing `dot64` model and its `(2 * n - 1) * 2^-52` absolute
error budget.  The empty input returns exact positive zero.  WebAssembly core
has no fused multiply-add instruction, so no contraction is permitted.

### Public contract

The hypotheses will keep machine safety separate from numerical safety:

- the two logical lists have equal length `n` and are represented by the
  memory words starting at the supplied base pointers;
- every address used by an eight-byte load is within linear memory and is
  obtained without 32-bit wrap; the final unused post-load increment may wrap
  at exactly `2^32`;
- the input words are finite binary64 values with explicit magnitude bounds;
- intermediate products and prefix accumulators satisfy either the existing
  recursive safety predicate or a proved aggregate sufficient condition.

The conclusion will be a `SmallStep.TerminatesWith` result stating that the
returned word is the pure modeled dot fold, the read-only memory is unchanged,
the word is finite, and, for nonempty inputs,

```text
|IEEE64.value result - exactDot inputs|
  <= (2 * n - 1) * 2^-52.
```

The exact generated function is the proof target.  Reproducible Rust source,
the pinned compiler, the emitted WAT, and the generated `Program.lean`
fidelity check establish artifact provenance, but the theorem will not claim
that rustc itself is verified.

### Ordered checkpoints

1. **Memory and load interface.**  Reuse `Mem.words64`, `array64At`, and the
   separation-logic heap layer.  Generalize the existing indexed `u64` load
   helper to an ownership-preserving `f64.load` theorem, and prove the required
   slot-address, nonwrap, and physical-page bounds.  Add a two-array read-only
   interface with explicit separation assumptions.
2. **Exact artifact and regressions.**  Add the smallest dedicated Rust
   binary64 dot-product crate supported by the pinned verifier pipeline,
   inspect the exact compiler output, emit its `Program.lean`, and record the
   artifact identity.  Add deterministic zero-, one-, and multi-element
   execution checks plus boundary and trap regressions.  If compiler output
   uses unsupported instructions, adjust the isolated crate/profile rather
   than weakening the semantic target.
3. **Total loop execution.**  Prove the generated loop with finite relational
   `SmallStep.Steps` traces for its exit and iteration branches, indexed by the
   current array position, pointers, countdown, and modeled accumulator and
   measured by the remaining element count.  Use `terminatesWith_of_loop` to
   assemble those exact iterations into an axiom-clean, fuel-independent
   execution theorem.  The invariant preserves both memory views, proves the
   load-pointer/no-wrap equations, and identifies the accumulator with the
   modeled prefix dot product.
4. **Absolute numerical result.**  Prove the prefix/list algebra needed to
   connect the loop invariant to `dot64` and `dot64Exact`.  Compose the exact
   execution theorem with `dot64_real_error`, including an exact empty-list
   branch, to obtain the finite-result and `(2 * n - 1) * 2^-52` WAT theorem.
5. **Aggregate safety.**  Replace per-stage rounded-value obligations at the
   public boundary with sufficient exact-real conditions.  Provide an
   absolute-mass condition and a uniform envelope corollary of the form
   `n * A * B + (2 * n - 1) * epsilon <= 1`.  These results must construct the
   existing recursive safety predicate and leave only proof-producing real or
   rational arithmetic for concrete clients.
6. **Scale-aware strengthening.**  Derive local normal-result relative
   roundoff with `u = 2^-53` from the pure IEEE64 rounder, then prove the
   standard dot-product bound
   `gamma (2 * n - 1) * sum |a_i * b_i|`, where
   `gamma k = k * u / (1 - k * u)` and `k * u < 1`.  State normality,
   no-underflow, no-overflow, and nonzero-exact-result assumptions explicitly.
   Add the corresponding condition-number relative-error corollary.  A mixed
   subnormal term is a follow-up if it cannot be kept reviewable in the same
   checkpoint; it must not weaken the already general absolute theorem.
7. **Evaluation and final validation.**  Add reproducible tests at lengths
   `0`, `1`, `2`, `4`, `16`, `64`, and `256`, covering exact powers of two,
   mixed signs, cancellation, signed zero, subnormals, binade boundaries,
   headroom boundaries, page-boundary loads, address wrap, and out-of-bounds
   traps.  Record proof assurance, proven-bound quality, clean/warm build cost,
   and regression cost separately.  Fixed-length external comparisons must
   use the same non-fused expression and assumptions and must not imply that
   another tool proves WAT control flow or memory semantics.

Every checkpoint must build with exact Lean `4.34.0-rc2`, pass its focused
interpreter and CodeLib targets, pass `git diff --check` and changed-source
proof-hole scans, and include `#print axioms` for its public general theorems.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted in those
reports.  Native IEEE and independent-engine comparisons remain regression
oracles, never theorem premises.  Each passing checkpoint is committed,
published immediately, fetched, and verified by comparing the remote and
local Git trees.

### Current flagship status

The agenda is recorded and checkpoint 1 is complete.  The reusable relational
memory layer now proves slot addresses/readback, physical in-bounds access, and
the exact authoritative `f64.load` transition for an indexed `Mem.words64`
view while preserving the complete machine store.

The initially planned total-WP formulation was tested and rejected for this
branch because rebuilding its pinned Iris dependencies reproduces the existing
`COFESolver` and `MaxPrefixList` type errors already recorded in the journal.
The flagship execution proof will instead use explicit relational
`SmallStep.Steps` iteration traces plus `terminatesWith_of_loop`.  This remains
an authoritative, fuel-independent total-correctness proof and avoids coupling
the numerical milestone to an unrelated dependency failure.

Checkpoint 2 is complete.  The dedicated Rust crate compiles to a 219-byte
binary with one call-free countdown loop, no stores or panic paths, an exact
positive-zero empty branch, and one initial multiplication followed by one
multiplication and one addition per tail element.  Its generated Lean AST is
checked against the decoded WAT by the existing fidelity guard.  Generated
artifact support is now split into a small `CodeLib.GeneratedCore`, while the
legacy `CodeLib.Generated` wrapper retains the full proof imports for existing
modules.  This lets the exact artifact build without entering the unrelated
pinned-Iris failure and keeps old generated proofs source-compatible.

Two numerical prerequisites were also completed independently while the
operational proof was being developed.  The aggregate layer now constructs
`Dot64Safe` from either exact absolute mass or a uniform `n * A * B` envelope,
and the total-list layer covers the exact empty branch as well as the
nonempty `(2 * n - 1) * 2^-52` result.  These are checkpoints 4--5 support
lemmas; their final attachment to WAT execution still waits for checkpoint 3.

Checkpoint 3 is complete.  Exact relational traces cover the generated
zero-length branch, first product, singleton exit, continuing loop iterations,
and final iteration.  `terminatesWith_of_loop` assembles them into a
fuel-independent theorem for arbitrary binary64 bit patterns.  Its conclusion
is exactly `dot64List terms`, and equality of the complete final machine store
proves that both arrays and all unrelated state are preserved.  A separate
hypothesis-free theorem exposes the pre-load empty branch, and a proved
`initConfig` equality connects the proof configuration to function zero of the
generated module without native evaluation.

Checkpoints 4 and 5 are complete.  Three `TerminatesWith.mono` corollaries
attach the total-list numerical result to the unchanged exact execution trace:
one accepts the recursive `Dot64ListSafe` evidence, one accepts an exact
absolute-mass budget, and one accepts uniform left/right envelopes.  Each
retains the exact returned word and complete-store equality while adding
finiteness and the piecewise error budget (zero when empty and
`(2 * n - 1) * 2^-52` when nonempty).  A second export-linked numerical spec
records the aggregate-mass interface without weakening the raw operational
spec.

Checkpoint 6 is in progress.  Its first four independently validated
subcheckpoints derive `u = 2^-53` relative rounding directly from the integer
`roundScaledMagnitude` model and lifts it to binary64 addition.  This bound is
valid even for cancellation and subnormal exact sums because addition remains
on the common `2^-1074` grid.  The multiplication layer derives an adaptive
bound: relative `u` outside underflow, half a minimum subnormal below it, plus
a mixed global corollary.  The format-independent numerical layer now proves
the geometric accumulation inequalities and the standard
`gamma(k,u) = k*u/(1-k*u)` conversion for sequential multiply/add traces.
The pure binary64 instantiation is also complete: it proves the standard
`gamma(2*n-1,u)` forward bound using the canonical `dot64AbsMass`, plus a
condition-number relative-error corollary for nonzero exact results.  Attaching
these results to exact WAT execution remains the next publishable subcheckpoint.

The deterministic artifact-regression portion of checkpoint 7 is complete.
It now exercises every required runtime length and the signed-zero,
subnormal, tie-to-even, cancellation, headroom, page-boundary, address-wrap,
and out-of-bounds cases using exact result bit patterns.  These checks remain
regression oracles only.  The proof/bound/build-cost evaluation summary waits
until the WAT gamma attachment is complete.
