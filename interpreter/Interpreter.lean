module

public import Interpreter.Wasm
public import Interpreter.Wasm.Examples.Basic

@[expose] public section

/-!
# Interpreter — public surface

The Wasm formalisation lives in `Interpreter.Wasm`: typed AST,
fuel-bounded interpreter, `wp` framework, `TerminatesWith` predicate, and
WAT decoder. Downstream code should `import` this module (or transitively
via `CodeLib`).
-/
