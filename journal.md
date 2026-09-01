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
