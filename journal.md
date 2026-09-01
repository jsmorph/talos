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
