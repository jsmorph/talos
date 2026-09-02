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

/-- The named generated export resolves to the function index used by the
public entry theorems. -/
theorem dotExport : «module».findExport "dot" = some 0 := by
  rfl

/-- Raw operational contract for the generated export.  The uniform memory
premises keep the quantified API simple and cover every dereferenced slot;
the final, unused pointer increment may wrap exactly at `2^32`.  For zero
length, `Proof.f64Dot_empty_terminates` removes every view, address, and
capacity premise.

Informal spec:
For two equal-length arrays represented by the supplied memory views, execute
the generated dot-product export, return the exact pure IEEE64 list fold, and
preserve the complete machine store.
-/
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
    SmallStep.initConfig { module := «module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (Proof.configFromStore wasm left right
          (UInt32.ofNat terms.length)) ∧
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
  exact Proof.f64Dot_export_terminates wasm left right terms hleftView hrightView
    hleftFit hrightFit hleftCapacity hrightCapacity

/-- Numerical contract for the generated export.  Besides the raw functional
result and complete store preservation, it exposes an exact-real aggregate
headroom condition and proves finiteness plus the full primitive-error budget.

Informal spec:
For two equal-length binary64 arrays whose dereferenced slots fit linear memory
and the 32-bit address space, return the separately rounded dot product without
changing the machine store; the unused final pointer increment may wrap at the
exact `2^32` boundary.  If every input is finite and unit-bounded, and the
exact absolute-product mass plus the `(2n - 1) * 2^-52` primitive-error budget
fits in the unit interval, the returned word is finite and lies within that
budget of the exact real dot product.
-/
@[spec_of "rust-exported" "f64_dot::dot"]
def F64DotNumericalSpec : Prop :=
  ∀ (wasm : Store Unit) (left right : UInt32)
      (terms : List (UInt64 × UInt64)),
    wasm.mem.words64 left terms.length = terms.map Prod.fst →
    wasm.mem.words64 right terms.length = terms.map Prod.snd →
    left.toNat + 8 * terms.length ≤ UInt32.size →
    right.toNat + 8 * terms.length ≤ UInt32.size →
    left.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536 →
    right.toNat + 8 * terms.length ≤ wasm.mem.pages * 65536 →
    CodeLib.Numerical.Kernels.Dot64UnitInputs terms →
    CodeLib.Numerical.Kernels.dot64AbsMass terms +
        CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1 →
    SmallStep.initConfig { module := «module», host := {} } 0 wasm
        [.i32 (UInt32.ofNat terms.length), .i32 right, .i32 left] =
        .ok (Proof.configFromStore wasm left right
          (UInt32.ofNat terms.length)) ∧
      SmallStep.TerminatesWith
        (Proof.configFromStore wasm left right (UInt32.ofNat terms.length))
        (fun values store =>
          values = [.f64 (CodeLib.Numerical.Kernels.dot64List terms)] ∧
            store = (Proof.configFromStore wasm left right
              (UInt32.ofNat terms.length)).store ∧
            CodeLib.IEEE64.Finite
              (CodeLib.Numerical.Kernels.dot64List terms) ∧
            |CodeLib.IEEE64.value
                (CodeLib.Numerical.Kernels.dot64List terms) -
                CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
              CodeLib.Numerical.Kernels.dot64ListErrorBudget terms)

/-- The aggregate absolute-mass numerical contract attached independently to
the same generated Rust export as the raw operational contract. -/
@[proves Project.F64Dot.Spec.F64DotNumericalSpec]
theorem provesNumerical : F64DotNumericalSpec := by
  intro wasm left right terms hleftView hrightView hleftFit hrightFit
    hleftCapacity hrightCapacity hinputs hbudget
  exact Proof.f64Dot_export_terminates_real_error_of_abs_mass
    wasm left right terms hleftView hrightView hleftFit hrightFit
      hleftCapacity hrightCapacity hinputs hbudget

#print axioms proves
#print axioms provesNumerical
#print axioms dotExport

end Project.F64Dot.Spec
