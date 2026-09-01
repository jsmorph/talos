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
