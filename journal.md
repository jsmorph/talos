# Floating-Point Verification Work Journal

## 2026-09-01: Baseline and plan

- Confirmed that local `main`, `origin/main`, and `upstream/main` are at Talos
  commit `24047c6`.
- Confirmed that `update-lean-4.34` contains that upstream commit and pins all
  Lean packages to `leanprover/lean4:v4.34.0-rc2`.
- Created `float-associativity-verification` from commit `fda69ca`.
- Inspected the current floating-point implementation, WAT decoder, validation,
  small-step semantics, lifting rules, worked examples, and
  `CodeLib.IEEE32.Exec`.
- Talos already executes `f32.add`, `f32.sub`, and `f32.abs`.  The existing
  numerical bridge covers comparisons and saturating conversion through five
  explicit axioms; it does not model addition, subtraction, real values, or
  roundoff.
- Selected the initial theorem scope: finite `f32` inputs bounded in absolute
  value by one, with epsilon `2^-20`.

### Next work

Add the WAT program, decoder checks, executable examples, and symbolic
small-step execution theorem.

## 2026-09-01: Decoded associativity-gap program

- Added a hand-written WAT module exporting `assoc_gap(f32, f32, f32) -> f32`.
- Added decidable checks for the decoded signature, export, and exact
  instruction sequence.
- Added an exact example using `1/2`, `1/4`, and `1/8`; its gap is positive
  zero.
- Added a rounding example using `1`, `2^-24`, and `2^-24`; its gap is
  `2^-23` because ties-to-even discards the two addends when they are added to
  one separately.

### Validation

- Installed the exact `v4.34.0-rc2` release locally because the workspace did
  not provide Lean or Lake.
- Supplied the executable path normally obtained from `/proc/self/exe`, which
  this sandbox does not expose.  Lean reported commit
  `6a10ac8c22beadecabdbb0919c2b50214762f91d`, and Lake reported Lean
  `4.34.0-rc2`.
- `lake build Interpreter.Wasm.Examples.FloatAssociativity` passed.  The first
  build compiled the interpreter and downloaded the dependencies pinned in the
  Lean 4.34 manifest.

### Next work

Add the symbolic execution and total-correctness theorems.

## 2026-09-01: Symbolic execution

- Defined the symbolic raw-bit result as the exact composition of Talos
  `f32Add`, `f32Sub`, and `f32Abs` operations.
- Added an explicit configuration and related it to entry zero of the decoded
  WAT module through `SmallStep.initConfig`.
- Added a thirteen-transition relational trace for arbitrary input bit
  patterns.
- Packaged the trace as fuel-independent `SmallStep.TerminatesWith` and
  `SmallStep.PartiallyMeets` theorems.

### Validation

- `lake build Interpreter.Wasm.Examples.FloatAssociativity` passed under the
  exact Lean 4.34.0-rc2 toolchain.
- The build rechecked the decoded-module connection, arbitrary-input trace,
  termination theorem, and partial-correctness theorem.

### Next work

Define a pure binary32 value and rounding model that can support an axiom-free
roundoff theorem and can be related directly to the interpreter operations.

## 2026-09-01: Pure binary32 addition and subtraction

- Added a proof-visible binary32 decomposition into sign, exponent, and
  fraction fields.
- Represented every finite value exactly as a signed integer multiple of
  `2^-149`, so the pre-rounding addition is integer addition.
- Implemented round-to-nearest, ties-to-even for the normal and subnormal
  ranges, including significand carry and overflow to infinity.
- Implemented IEEE special cases for signed zero, exact cancellation,
  infinity, and canonical NaN.
- Replaced the interpreter's native `Float32` implementations of `f32Add` and
  `f32Sub` with the pure operations.  This also makes scalar and SIMD uses of
  those operations proof-visible.
- Added edge-case comparisons and 4,096 deterministic full-width comparisons
  each for addition and subtraction against the native `Float32` operations.

### Validation

- `lake build Interpreter.Wasm.Examples.IEEE32
  Interpreter.Wasm.Examples.FloatAssociativity` passed under Lean 4.34.0-rc2.
  This checked all 8,232 differential cases and both end-to-end WAT examples.
- A default `lake build` compiled the updated semantics, `FloatOps`,
  `FloatAssociativity`, `SmallStep`, and the other reached Talos examples, but
  did not complete because Lean exited with code 139 while compiling the
  unrelated, unchanged `Interpreter.Wasm.Examples.MemReplace`.  Retrying that
  single file in isolation reproduced the code-139 compiler crash.

### Next work

Prove the real-value decoding and rounding-error lemmas for bounded finite
inputs, then apply them to the associativity-gap expression.

## 2026-09-01: Axiom-free binary32 rounding bound

- Re-expressed sign, exponent, fraction, finite encoding, negation, and
  absolute value with `UInt32.toNat` arithmetic.  This is extensionally the
  same bit representation, while exposing the field equations to ordinary
  Lean arithmetic proofs.
- Added `CodeLib.IEEE32.Roundoff` as a codelib root.
- Proved the encoder's sign, exponent, fraction, finiteness, scaled-magnitude,
  and signed scaled-value equations.
- Proved bounds for round-to-nearest, ties-to-even, including the exact two
  possible error directions.
- Proved that `roundScaledMagnitude` returns a finite binary32 number whenever
  the exact magnitude is below `2^151`, and that its error is at most `2^126`
  units of `2^-149`.  The proof handles subnormal results, exact results,
  ordinary rounding, and significand carry without floating-point axioms.
- Removed an attempted bit-vector proof path after `bv_decide` triggered a Lean
  code-139 crash in this environment; the committed proof uses standard
  natural- and integer-arithmetic lemmas instead.

### Validation

- `lake build CodeLib.IEEE32.Roundoff` passed under Lean 4.34.0-rc2.
- `lake build Interpreter.Wasm.Examples.IEEE32
  Interpreter.Wasm.Examples.FloatAssociativity` passed again.  This rechecked
  all 8,232 differential add/sub comparisons and the WAT examples after the
  proof-oriented representation refinement.

### Next work

Lift the unsigned magnitude theorem to signed addition, subtraction, and
absolute value; prove the associativity-gap bound; then compose it with the
symbolic termination theorem.

## 2026-09-01: End-to-end associativity-gap verification

- Proved signed rounding, finite addition, sign negation, subtraction, and
  absolute-value specifications from the unsigned rounding theorem.
- Expressed sign negation and absolute value through the verified field
  encoder.  This preserves exponent, fraction, and NaN payload bits by
  construction and keeps the operations directly accessible to proofs.
- Proved `assocGap_scaled_spec`: for finite inputs whose magnitudes are at most
  one, the complete result is finite, nonnegative, and below `2^129` integer
  units of `2^-149`.
- The error accounting uses at most one `2^126`-unit rounding error for each
  of the two additions on each association path and one for the final
  subtraction.  Thus the gap is at most `5 * 2^126`, strictly below `2^129`.
- Defined the real-valued `epsilon` as `2^-20` and proved
  `assocGap_output_lt_epsilon` for the exact interpreter result.
- Strengthened the arbitrary-input symbolic execution theorem to
  `assocGap_terminates_lt_epsilon`, a fuel-independent `TerminatesWith`
  theorem whose returned value is finite and below epsilon.

### Validation

- `lake build CodeLib.IEEE32.Roundoff` passed under Lean 4.34.0-rc2.
- Rebuilding after the final proof-friendly sign-field definition compiled
  `Interpreter.Wasm.SmallStep` successfully in 339 seconds.
- `lake build Interpreter.Wasm.Examples.IEEE32
  Interpreter.Wasm.Examples.FloatAssociativity` passed after all arithmetic
  changes, rechecking the 8,232 native differential comparisons and the WAT
  examples.
- Added and passed 4,096 full-width checks each showing that the proof-friendly
  negation and absolute-value implementations exactly equal sign-bit flip and
  sign-bit clear, respectively.
- `#print axioms` for both final numerical theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  There is no `sorryAx`, no native
  floating-point bridge axiom, and no dependency on `CodeLib.IEEE32.Exec`.

### Outstanding repository issue

The previously recorded code-139 compiler crash in the unchanged
`Interpreter.Wasm.Examples.MemReplace` still prevents claiming a successful
default interpreter-wide build.  A final default codelib build also reached
and replayed `CodeLib.IEEE32.Roundoff`, then failed in unchanged targets:
type errors in the pinned Iris `COFESolver` and `MaxPrefixList` modules, plus
code-139 compiler exits in `CodeLib.IEEE32.Exec` and `CodeLib.RustStd.Frame`.
All modules changed by this work and all direct dependents used by the
verification pass.

## 2026-09-01: NaN and infinity specifications

- Added `CodeLib.IEEE32.SpecialValues` as a separately buildable codelib root.
- Proved the exponent, fraction, sign, and classification equations for the
  canonical NaN and both signed infinities.
- Proved that sign negation and absolute value preserve NaN classification;
  addition and subtraction canonicalize any NaN operand.
- Proved finite/infinity addition and subtraction identities, same-sign
  infinity addition, opposite-sign infinity subtraction, and the invalid
  cases `+inf + -inf` and `inf - inf`, which return the canonical NaN.
- Derived the infinity constant's field equations through the ordinary
  encoder, with only kernel-decided equality for the two concrete encodings.

### Validation

- `lake build CodeLib.IEEE32.SpecialValues` passed under Lean 4.34.0-rc2.

### Next work

Prove the exact round-to-nearest overflow threshold and lift it to finite
addition and subtraction.

## 2026-09-01: Binary32 overflow specifications

- Defined the exact round-to-nearest, ties-to-even overflow threshold as
  `(2^25 - 1) * 2^252 = 2^277 - 2^252` scaled units.  In real values this is
  `2^128 - 2^103`, the midpoint immediately above the largest finite binary32
  value.
- Proved that magnitudes from the midpoint up to `2^277` round their odd
  maximal significand upward to infinity.
- Proved independently that every magnitude at least `2^277` necessarily
  packs an exponent field of at least 255 and therefore becomes infinity.
- Combined the ranges in `roundScaledMagnitude_overflows`, preserving the sign
  of the exact result.
- Lifted the result to `add_overflow` and `sub_overflow` for finite operands.
  Each theorem returns the correctly signed infinity when the exact scaled
  result reaches the midpoint threshold.
- Added executable checks at the positive and negative tie, for subtraction at
  the tie, and immediately below the positive tie.  Both the pure model and
  native `Float32` agree in all four cases.

### Validation

- `lake build CodeLib.IEEE32.SpecialValues` passed under Lean 4.34.0-rc2.
- `lake build Interpreter.Wasm.Examples.IEEE32` passed with the new boundary
  checks.
- `#print axioms` for the NaN, infinity, rounder-overflow, addition-overflow,
  and subtraction-overflow theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound` as applicable.  There is no `sorryAx`
  and no dependency on the floating-point bridge axioms.

## 2026-09-02: Full operation roadmap

- Restored `float-associativity-verification` from the pushed fork after the
  transient workspace was cleared.  The restored head is `8b8cc16`.
- Expanded `plan.md` with staged work for f32 multiplication, division, square
  root, comparisons and selection, conversions and integral rounding, f64,
  SIMD, and algorithm-level transcendental verification.
- Required every operation milestone to include proof-visible interpreter
  semantics, differential tests, operation specifications, and at least one
  fuel-independent theorem about an example WAT program.
- Kept the toolchain fixed at `leanprover/lean4:v4.34.0-rc2`.

### Next work

Generalize exact rounding to dyadic products and implement binary32
multiplication, including special values, overflow, gradual underflow, native
differential tests, and an example-program theorem.

## 2026-09-02: Representative operation-roadmap implementation

- Generalized binary32 rounding from scaled integers to exact dyadics, exact
  rational quotients, and an exact integer-square-root midpoint test.
- Replaced native f32 multiplication, division, square root, comparisons,
  min/max, copysign, integral rounding, and integer conversions with the pure
  `Wasm.IEEE32` implementation.  Trapping conversion classification now uses
  the same pure NaN predicate in big-step, small-step, and weakest-precondition
  semantics.
- Added a pure `Wasm.IEEE64` model for scalar arithmetic, square root,
  comparison, min/max, copysign, and integral rounding.  Native f64 conversion
  operations remain an explicit follow-up seam.
- Added differential regression suites against native IEEE arithmetic.  The
  direct suites passed 4,105 cases for each f32 operation family and 1,031
  cases across f64 scalar operations.  Committed suites cover 4,096 f32
  conversion inputs and 1,024 full-width plus seven f64 edge inputs.
- Added hand-written WAT programs and fuel-independent small-step theorems for
  f32 multiplication, division, square root, clamp, nearest, signed i32
  conversion, f64 multiplication, `f32x4.mul`, `f64x2.mul`, and the cubic sine
  polynomial `x - x^3 / 6`.  The executable round-trip program also checks the
  exact/inexact i32 boundary.
- Added CodeLib specifications for finite exact products and quotients,
  positive square root, NaN/infinity/zero behavior, overflow, gradual
  underflow, comparison and signed-zero selection, conversion saturation,
  integral ties-to-even, lane-wise SIMD, and algorithm-level sine execution.
- Replaced `native_decide` with kernel `decide` in scalar examples where the
  kernel evaluator reduces the operation.  Concrete positive-square-root and
  SIMD examples retain `native_decide` as regression-oracle theorems because
  `Nat.sqrt` does not reduce through their decidable equalities; the general
  operation and program specifications remain independent of those examples.

### Validation so far

- All new interpreter example targets pass with Lean 4.34.0-rc2.
- The targeted CodeLib builds pass for multiplication, division, square root,
  selection, integral rounding, conversions, binary64 operations, SIMD, and
  the transcendental example.
- `Interpreter.Wasm.Wp.Atomic` passes after its four f32 truncation rules were
  aligned with the proof-visible NaN classifier.
- `CodeLib.IEEE32.Exec` still reaches Lean's previously recorded code-139
  compiler crash after all interpreter dependencies build.  Its five legacy
  compatibility axioms remain isolated from the new operation specifications.

### Final validation and delivery

- A combined interpreter build passed all new IEEE32/IEEE64 regression suites,
  all scalar/SIMD/polynomial WAT examples, and `Interpreter.Wasm.Wp.Atomic`
  in 3,058 jobs.
- A combined codelib build passed all nine new specification roots in 3,067
  jobs.  Axiom reports for the general operation and exact program theorems
  contain only `propext`, `Classical.choice`, and `Quot.sound` as applicable;
  they do not depend on `CodeLib.IEEE32.Exec` or its compatibility axioms.
- Concrete positive-square-root, SIMD lane-vector, binary64 arithmetic, and
  half-input polynomial examples use `native_decide` only as executable test
  evidence.  The corresponding general semantics/program theorems are checked
  independently of those native-oracle theorems.
- `git diff --check` passed, no new source file contains `sorry` or `admit`,
  and the worktree was clean after delivery.
- Pushed the byte-verified interpreter tree at `028d556` and the CodeLib,
  plan, and journal tree at `1abfe86` to
  `origin/float-associativity-verification`.  Local and remote Git tree hashes
  matched after each branch update.

## 2026-09-02: Strengthening phase resumed

- Restored the pushed `float-associativity-verification` branch at `3962f07`
  after workspace pruning and installed the exact Lean 4.34.0-rc2 release
  toolchain.  Dependency and mathlib cache restoration is in progress.
- Added proof-visible binary64 integer conversions: signed and unsigned
  `i32`/`i64` conversion to f64, trapping conversion back to both integer
  widths, and all saturating variants.  The interpreter now delegates those
  instructions to `Wasm.IEEE64`; native `Float` conversions are retained only
  as differential-test oracles.
- Added deterministic binary64 conversion comparisons and boundary tests, a
  CodeLib conversion specification, special-value theorems, ties-to-even
  examples, and a termination theorem for the conversion round-trip program.
- Replaced the five declarations in `CodeLib.IEEE32.Exec` with proved
  compatibility theorems over the authoritative IEEE32 semantics.  Reworked
  the large-positive and large-negative i32 saturation results around exact
  scaled-value inequalities, eliminating the exhaustive bitvector proof, and
  removed an unused `Exec` import from `FloatRound`.

### Validation and checkpoints

- `lake build Interpreter.Wasm.Examples.IEEE64
  Interpreter.Wasm.Examples.FloatOps` passed.  The native differential suite
  accepts all 1,031 scalar cases plus the added conversion comparisons and
  boundaries.
- `lake build CodeLib.IEEE64.Conversions` passed in 3,050 jobs.  Its public
  conversion definitions, finite truncation theorem, saturation theorem, and
  direct small-step round-trip theorem use only standard Lean logical axioms.
- Committed the proof-visible f64 seam as `d1d1f9b` locally and pushed the
  byte-identical tree as remote commit `8a4f27f`.
- `lake build CodeLib.IEEE32.Exec` now passes in 3,051 jobs instead of exiting
  with code 139.  Axiom reports show that `beq_ax`, `isNaN_ax`, `ble_ax`,
  `blt_ax`, and `satI32S_eq` depend on no axioms.  The two general saturation
  results use only `propext`, `Classical.choice`, and `Quot.sound`.
- A requested build of `Project.FloatTrunc.Spec` and
  `Project.FloatRound.Spec` replayed the passing `Exec` target, then was
  blocked by the already recorded type errors in pinned Iris
  `Iris.Algebra.COFESolver`.  The failure occurs before either project target
  and is unrelated to this change.
- Added `CodeLib.IEEE32.Rounders` and proved a quantitative contract for the
  interpreter's exact ties-to-even dyadic rounder at binary32 scale.  The
  theorem covers exact packing, normal rounding, significand carry, gradual
  underflow, signs, and finiteness without a floating-point oracle.
- Lifted that contract through `Wasm.IEEE32.mul`: for finite inputs with real
  magnitudes at most one, the modeled f32 result is finite and differs from
  exact real multiplication by at most `2^-23`.  This theorem shares the
  proof-visible operation used by the existing hand-written WAT multiplication
  program.
- `lake build CodeLib.IEEE32.Multiplication` passes in 3,051 jobs under exact
  Lean 4.34.0-rc2.  Axiom reports for the new rounder and multiplication error
  theorems contain only standard logical axioms (`propext`,
  `Classical.choice`, and `Quot.sound`); no compatibility axiom or `sorryAx`
  remains.
- Proved the quotient/remainder error contract for `roundQuotient`, including
  exact-half parity, and lifted it through every packing branch of
  `roundRationalMagnitude`.  For a rational scaled magnitude no larger than
  one, the result is finite and its cleared-denominator error is uniformly
  bounded by the binary32 unit-roundoff budget.
- Added `div_real_error` and `div_program_terminates_real_error`.  For finite
  inputs with a nonzero denominator and numerator magnitude no larger than the
  denominator magnitude, modeled f32 division and the decoded WAT program are
  within `2^-23` of exact real division.
- `lake build CodeLib.IEEE32.Division` passes in 3,051 jobs under exact Lean
  4.34.0-rc2.  Its rounder, operation, and fuel-independent program error
  theorems use only standard Lean logical axioms.
- Pushed the division checkpoint as remote commit `8d5234c`; a fetch confirmed
  that its Git tree is byte-identical to the local committed tree.
- Proved the real half-output-unit contract for `roundSqrtIntegral` directly
  from its integer midpoint-square comparison.  The theorem passes in about
  six seconds and uses only standard logical axioms.
- The first monolithic proof that exponent/fraction packing preserves the
  square-root contract closed all elaboration goals, but Lean's kernel rejected
  its deeply nested reduction term even with `maxRecDepth` raised from 8,192 to
  65,536.  Axiom inspection exposed the rejected declaration; no `sorry` or
  compatibility axiom was introduced.  The implementation is now being
  factored through the existing exact `roundScaledMagnitude` packer to obtain a
  smaller kernel-checkable proof term, after which the native and boundary
  square-root suites will be rerun.

## 2026-09-02: Quantitative square-root checkpoint

- Refactored `roundSqrtMagnitude` to feed its exactly representable rounded
  scaled integer through the shared `roundScaledMagnitude` packer.  This keeps
  the executable IEEE32 result unchanged while replacing the rejected
  hand-expanded packing proof with a compact reusable exact-packing argument.
- Proved `roundSqrtIntegral_real_error` from the integer midpoint-square test,
  then proved `roundSqrtMagnitude_spec`: inputs no larger than `2^149` produce
  a finite positive result whose scaled magnitude is within `2^126` of the
  exact scaled real square root.
- Added `sqrt_real_error`.  For a nonzero, positive, finite binary32 input no
  larger than one, the modeled `f32.sqrt` differs from `Real.sqrt` by at most
  the fixed real epsilon `2^-23`.
- Added `sqrt_program_terminates_real_error`, attaching the same quantitative
  result to the decoded hand-written WAT program's fuel-independent execution
  theorem.
- `lake build Interpreter.Wasm.Examples.FloatSquareRoot
  Interpreter.Wasm.Examples.IEEE32` passed, rebuilding the affected IEEE32 and
  small-step semantics.  `lake build CodeLib.IEEE32.SquareRoot` passed in 3,051
  jobs under exact Lean 4.34.0-rc2.
- Axiom reports for the new rounder, operation, and WAT theorems contain only
  `propext`, `Classical.choice`, and `Quot.sound`.  `git diff --check` passed,
  and the changed source contains no `sorry`, `admit`, or new axiom.
- Next: push this checkpoint, then strengthen the cubic sine program from its
  fixed-input analytic result to a nontrivial interval theorem that combines a
  Taylor remainder with the primitive f32 roundoff budgets.

## 2026-09-02: Nontrivial-interval sine checkpoint

- Added reusable `add_real_error` and `sub_real_error` theorems.  Finite
  operands of magnitude at most one produce finite results within `2^-23` of
  exact real addition or subtraction.
- Strengthened the cubic sine example from the exact input zero to every
  finite binary32 input in `[-1/2, 1/2]`.
- Proved the real approximation component using Mathlib's cubic sine bound:
  `|(x - x^3 / 6) - sin x| ≤ 1/3200` throughout the interval.
- Followed the WAT instruction order and composed the two multiplication
  bounds, division-by-six bound, and final subtraction bound.  A conservative
  floating-point contribution of `3 * 2^-23`, added to the analytic term, is
  strictly less than the fixed `sineIntervalEpsilon = 2^-11`.
- Added `sinResult_interval_error` for the executable IEEE32 expression and
  `sin_small_program_interval_error` for the decoded program's
  fuel-independent `SmallStep.TerminatesWith` execution.
- `lake build CodeLib.IEEE32.Transcendental` passed in 3,170 jobs under exact
  Lean 4.34.0-rc2.  Axiom reports for the reusable add/sub contracts, analytic
  bound, result theorem, and WAT theorem contain only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or compatibility axiom is
  present.
- Next: push this checkpoint, then run the combined affected-root builds,
  source scans, and local/remote tree verification for final delivery.

## 2026-09-02: Strengthening agenda completed

- Pushed the square-root checkpoint as `9f32c23` and the nontrivial-interval
  sine checkpoint as `465aef5`.  After each update, a fetch confirmed the
  remote Git tree was byte-identical to the local committed tree.
- Confirmed the executable compiler directly reports Lean `4.34.0-rc2`
  (release commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`).
- The combined interpreter validation passed
  `Interpreter.Wasm.Examples.IEEE32`, `IEEE64`, `FloatOps`, multiplication,
  division, square root, and the sine polynomial.  This covers the native
  differential suites and all affected decoded WAT examples.
- The combined CodeLib validation passed 3,180 jobs for IEEE64 conversions,
  IEEE32 compatibility theorems, roundoff and rounders, multiplication,
  division, square root, and transcendental specifications.
- Axiom output reconfirmed that the five former declarations `beq_ax`,
  `isNaN_ax`, `ble_ax`, `blt_ax`, and `satI32S_eq` depend on no axioms.  Every
  new general numerical and execution theorem reports only standard Lean
  logical axioms.  Native-oracle axioms occur only in the older explicitly
  concrete regression examples and are not dependencies of the general
  results.
- The final source scan found no `sorry`, `admit`, or axiom declaration in the
  affected semantics and specification files.  `git diff --check` passed.
- All seven items in the current execution agenda are complete.  This final
  documentation update records the validated state for the pushed branch.

## 2026-09-02: Quantitative kernels phase started

- Accepted the next three priorities in order: quantitative f64 arithmetic,
  reusable error-composition lemmas, and representative f32/f64 numerical
  kernels.
- Confirmed the branch begins clean at remote commit `b73c860` and remains
  pinned to exact Lean 4.34.0-rc2.
- Phase 1 will extend the existing pure binary64 semantics rather than add a
  second arithmetic model.  Each public error result will be paired with a
  decoded-WAT execution theorem where an example module exists or is added.
- Passing phases will be committed and pushed separately.  Native floating-
  point evaluation remains confined to deterministic regression examples.

### Binary64 roundoff foundation

- Added a binary64 real-value interpretation and proved finite decoding,
  scaled-magnitude packing, sign preservation, and bounded scaled-value
  rounding through the existing integer ties-to-even primitive.
- Proved finite binary64 addition and subtraction differ from exact real
  arithmetic by at most `2^-52` when both inputs have magnitude at most one.
- Factored binary64 dyadic, rational, and square-root candidate packing through
  the shared `roundScaledMagnitude` implementation.  The 1,031-case native
  differential suite passed, followed by the full affected interpreter build;
  `Interpreter.Wasm.SmallStep` rebuilt successfully in 364 seconds.
- `lake build CodeLib.IEEE64.Roundoff` passed under Lean 4.34.0-rc2.  Its
  public packing, addition, and subtraction theorems report only standard Lean
  logical axioms.

### Binary64 multiplication checkpoint

- Added the reusable binary64 dyadic-rounder contract.  A product small enough
  to avoid overflow is finite, preserves its computed sign, and has
  cleared-denominator error at most `2^2096`.
- Proved `mul_real_error`: multiplying finite binary64 inputs whose absolute
  values are at most one produces a finite result within `2^-52` of the exact
  real product.
- Attached the same bound to the existing decoded hand-written f64
  multiplication WAT program through its fuel-independent termination theorem.
- `lake build CodeLib.IEEE64.Operations` passed under exact Lean 4.34.0-rc2.
  Axiom reports for the rounder, operation, and WAT theorems contain only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Next: commit and push this checkpoint, then prove the corresponding binary64
  rational-rounding and division contracts.

### Binary64 division checkpoint

- Recreated and proved `CodeLib.IEEE64.roundRationalMagnitude_spec`.  For a
  nonzero denominator and numerator at most `denominator * 2^1074`, the result
  is finite, preserves the requested sign, and has cleared-denominator scaled
  error at most `denominator * 2^1022`.
- Added a decoded hand-written `f64.div` WAT module, its explicit four-step
  `SmallStep.Steps` trace, and a fuel-independent `TerminatesWith` theorem.
- Added the finite-rounder equality, cleared-denominator error theorem,
  `divisionEpsilon = 2^-52`, real division error theorem, and the corresponding
  WAT execution/error theorem for finite inputs with a nonzero denominator and
  quotient magnitude at most one.
- `lake build CodeLib.IEEE64.Rounders` passed in 3,056 jobs under exact Lean
  4.34.0-rc2.  `lake build Interpreter.Wasm.Examples.Float64Division` passed
  in 15 jobs, and `lake build CodeLib.IEEE64.Operations` passed in 3,054 jobs.
- Axiom reports for the rational rounder and all new general division theorems
  contain only `propext`, `Classical.choice`, and `Quot.sound`.  The changed
  sources contain no `sorry`, `admit`, or new axiom, and `git diff --check`
  passes.
- Next: publish and fetch-verify this checkpoint, then prove binary64 square
  root and add the remaining direct f64 operation WAT examples.

### Binary64 square-root and operation-WAT checkpoint

- Proved `CodeLib.IEEE64.roundSqrtMagnitude_spec` by adapting the verified
  integer-midpoint argument to the binary64 scale and passing the exact
  candidate through `roundScaledMagnitude`.  Magnitudes at most `2^1074`
  produce a finite positive value within `2^1022` scaled units of the exact
  scaled real square root.
- Added `squareRootEpsilon = 2^-52`, the positive finite-operation theorem,
  the real square-root error theorem, and its decoded-WAT execution theorem.
- Added direct decoded WAT modules for `f64.sqrt`, `f64.add`, and `f64.sub`.
  Each has an explicit `SmallStep.Steps` trace and a fuel-independent
  `TerminatesWith` theorem; the addition and subtraction traces are connected
  to the existing binary64 `2^-52` real-error theorems.
- `lake build CodeLib.IEEE64.Rounders` passed in 3,050 jobs;
  `lake build Interpreter.Wasm.Examples.Float64SquareRoot` and
  `Interpreter.Wasm.Examples.Float64AddSub` each passed in 15 jobs; and
  `lake build CodeLib.IEEE64.Operations` passed in 3,056 jobs.  All commands
  used exact Lean 4.34.0-rc2.
- Axiom reports for the new rounder, square-root, addition-WAT, subtraction-WAT,
  and square-root-WAT theorems contain only `propext`, `Classical.choice`, and
  `Quot.sound`.  Phase 1 now has representative decoded-WAT theorems for all
  five requested binary64 arithmetic operations.
- Next: publish and fetch-verify this checkpoint, then add the reusable real
  error-composition layer and refactor the cubic sine proof to consume it.

### Reusable error-composition checkpoint

- Added `CodeLib.Numerical.ErrorComposition`, a format-independent real
  inequality layer for sums of perturbations, products with explicit operand
  magnitude budgets and the second-order term, division by an exact nonzero
  constant, and two sequential Horner steps.
- Added the new module to the CodeLib roots.  Refactored the existing f32 cubic
  sine interval proof to use the Horner, exact-division, and perturbation-sum
  results while preserving its finite-result and strict `2^-11` public bound.
- `lake build CodeLib.Numerical.ErrorComposition` passed in 3,032 jobs and
  `lake build CodeLib.IEEE32.Transcendental` passed in 3,171 jobs under exact
  Lean 4.34.0-rc2.
- Axiom reports for all four composition lemmas and the refactored sine result
  and WAT theorems contain only `propext`, `Classical.choice`, and
  `Quot.sound`.  `git diff --check` and the changed-source proof-hole scan pass.
- Next: publish and fetch-verify this checkpoint, then verify decoded f32
  affine/Horner and f64 dot-product numerical kernels.
