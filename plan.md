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
