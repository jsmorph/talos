import Interpreter.Wasm.Examples.Float64Multiplication
import Interpreter.Wasm.Examples.IEEE64
import Mathlib.Tactic

/-!
# Binary64 operation specifications
-/

namespace CodeLib.IEEE64

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

open Wasm
open Wasm.Float64Multiplication

def Finite (x : UInt64) : Prop := Wasm.IEEE64.isFinite x = true

theorem mul_nan_left {a : UInt64} (b : UInt64)
    (ha : Wasm.IEEE64.isNaN a = true) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.canonicalNaN := by
  simp [Wasm.IEEE64.mul, ha]

theorem mul_infinities (aSign bSign : Bool) :
    Wasm.IEEE64.mul (Wasm.IEEE64.infinity aSign)
        (Wasm.IEEE64.infinity bSign) =
      Wasm.IEEE64.infinity (aSign != bSign) := by
  cases aSign <;> cases bSign <;> decide

theorem sqrt_special_values :
    Wasm.IEEE64.sqrt 0x8000000000000000 = 0x8000000000000000 ∧
    Wasm.IEEE64.sqrt 0x7FF0000000000000 = 0x7FF0000000000000 ∧
    Wasm.IEEE64.sqrt 0xBFF0000000000000 = Wasm.IEEE64.canonicalNaN := by
  decide

theorem mul_program_exact (a b : UInt64) :
    SmallStep.TerminatesWith (mulConfig a b)
      (fun values _ => values = [.f64 (Wasm.IEEE64.mul a b)]) :=
  mul_terminates a b

theorem arithmetic_examples :
    Wasm.IEEE64.add 0x3FF0000000000000 0x3CA0000000000000 =
      0x3FF0000000000000 ∧
    Wasm.IEEE64.div 0x3FF0000000000000 0 = 0x7FF0000000000000 ∧
    Wasm.IEEE64.sqrt 0x4010000000000000 = 0x4000000000000000 := by
  native_decide

#print axioms mul_nan_left
#print axioms mul_infinities
#print axioms mul_program_exact
#print axioms arithmetic_examples

end CodeLib.IEEE64
