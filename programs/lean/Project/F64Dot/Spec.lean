import Project.F64Dot.Program

/-!
# Specification for `f64_dot`
-/

namespace Project.F64Dot.Spec

open Wasm

/- The generated artifact has one local, call-free exported function with the
expected ABI.  The quantitative total-correctness contract replaces this
scaffold in the loop-proof checkpoint. -/
#guard «module».imports.isEmpty
#guard «module».funcs.length == 1
#guard «module».findExport "dot" == some 0
#guard func0Def.params == [.i32, .i32, .i32]
#guard func0Def.locals == [.f64]
#guard func0Def.results == [.f64]

@[spec_of "rust-exported" "f64_dot::dot"]
def F64DotSpec : Prop :=
  True

end Project.F64Dot.Spec
