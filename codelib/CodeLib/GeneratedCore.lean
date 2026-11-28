module

public import CodeLib.Attrs
public import Interpreter.Wasm.LeanSyntax
public import Interpreter.Wasm.Decoder.Wat
public import Lean.Elab.Term
public meta import Interpreter.Wasm.Syntax
public import CodeLib.GeneratedToExpr
public meta import CodeLib.GeneratedToExpr
public meta import Interpreter.Wasm.Decoder.Wat

@[expose] public section

/-!
# Artifact support for generated Wasm modules

Generated `Program.lean` files import this module for the project attributes
and compact syntax that elaborates to ordinary Wasm AST literals.  It remains
independent of CodeLib's proof umbrella so artifact fidelity can be checked
without building unrelated proof libraries.
-/

namespace Wasm

open Lean Elab Term

/-- Decode a WAT file while elaborating and splice its complete Wasm AST into
the declaration as a literal expression. The source file therefore stays tiny,
while the resulting definition is just as reducible as a handwritten AST. -/
syntax (name := watModule) "watModule% " str : term

@[term_elab watModule] meta def elabWatModule : TermElab := fun stx _ => do
  let `(watModule% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let path : System.FilePath := pathSyntax.getString
  let source ← IO.FS.readFile path
  let module ← match Decoder.Wat.decodeForVerification source with
    | .ok module => pure module
    | .error message => throwError "WAT decoder rejected {path}: {message}"
  pure (toExpr module)

/-- Quote all module metadata except function declarations. Generated files
provide those separately so each function body remains immediately transparent
to existing `wp_*` tactics, while data segments and other bulky metadata do not
occupy committed source text. -/
syntax (name := watModuleMetadata) "watModuleMetadata% " str : term

@[term_elab watModuleMetadata] meta def elabWatModuleMetadata : TermElab := fun stx _ => do
  let `(watModuleMetadata% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let path : System.FilePath := pathSyntax.getString
  let source ← IO.FS.readFile path
  let module ← match Decoder.Wat.decodeForVerification source with
    | .ok module => pure module
    | .error message => throwError "WAT decoder rejected {path}: {message}"
  pure (toExpr { module with funcs := [] })

/-- Quote one function body directly. Unlike projecting it from a quoted
module list, this exposes the leading instruction to unification at reducible
transparency, which keeps the existing `wp_*` proof scripts working. -/
syntax (name := watFunctionBody) "watFunctionBody% " str num : term

@[term_elab watFunctionBody] meta def elabWatFunctionBody : TermElab := fun stx _ => do
  let `(watFunctionBody% $pathSyntax:str $indexSyntax:num) := stx
    | throwUnsupportedSyntax
  let path : System.FilePath := pathSyntax.getString
  let index := indexSyntax.getNat
  let source ← IO.FS.readFile path
  let module ← match Decoder.Wat.decodeForVerification source with
    | .ok module => pure module
    | .error message => throwError "WAT decoder rejected {path}: {message}"
  let some function := module.funcs[index]?
    | throwErrorAt indexSyntax
        "function index {index} is out of bounds for {path} ({module.funcs.length} functions)"
  pure (toExpr function.body)

/-- Decode the current WAT artifact and structurally compare the quoted kernel
expressions for its complete AST and the generated Lean module. This checks
every constructor, instruction, and immediate rather than merely pinning a
second copy of the WAT text inside `Program.lean`. -/
def checkWatFidelity (path : System.FilePath) (actual : Module) : IO Unit := do
  unless ← path.pathExists do
    throw (IO.userError s!"{path} is missing; cannot validate Program.lean provenance.")
  let source ← IO.FS.readFile path
  let expected ← match Decoder.Wat.decodeForVerification source with
    | .ok expected => pure expected
    | .error message => throw (IO.userError s!"{path} no longer decodes: {message}")
  unless toExpr actual == toExpr expected do
    throw (IO.userError
      s!"{path} decodes to a different Wasm module; re-run `lake exe verifier emit`.")

end Wasm
