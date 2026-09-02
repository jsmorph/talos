import Project.F64Dot.Proof

/-!
# Specification for `f64_dot`
-/

namespace Project.F64Dot.Spec

open Wasm

/- The generated artifact has one local, call-free exported function with the
expected ABI. -/
#guard «module».imports.isEmpty
#guard «module».funcs.length == 1
#guard «module».findExport "dot" == some 0
#guard func0Def.params == [.i32, .i32, .i32]
#guard func0Def.locals == [.f64]
#guard func0Def.results == [.f64]

@[spec_of "rust-exported" "f64_dot::dot"]
def F64DotSpec : Prop :=
  ∀ (wasm : Store Unit) (left right : UInt32)
      (terms : List (UInt64 × UInt64)),
    wasm.mem.words64 left terms.length = terms.map Prod.fst →
    wasm.mem.words64 right terms.length = terms.map Prod.snd →
    left.toNat + 8 * terms.length ≤ UInt32.size →
    right.toNat + 8 * terms.length ≤ UInt32.size →
    left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536 →
    right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536 →
    SmallStep.TerminatesWith
      (Proof.configFromStore wasm left right (UInt32.ofNat terms.length))
      (fun values store =>
        values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
          store = (Proof.configFromStore wasm left right
            (UInt32.ofNat terms.length)).store)

/-- The total functional contract attached to the generated Rust export. -/
@[proves Project.F64Dot.Spec.F64DotSpec]
theorem proves : F64DotSpec := by
  intro wasm left right terms hleftView hrightView hleftFit hrightFit
    hleftCapacity hrightCapacity
  exact Proof.f64Dot_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity

#print axioms proves

end Project.F64Dot.Spec
