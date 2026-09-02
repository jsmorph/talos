import CodeLib
import CodeLib.GeneratedCore

/-!
# Legacy proof support for generated Wasm modules

Existing generated `Program.lean` files import this compatibility module, which
re-exports both CodeLib's proof surface and the artifact support in
`CodeLib.GeneratedCore`. Newly generated artifacts import the core module
directly so checking their decoded AST does not build unrelated proof roots.
-/
