import CodeLib.IEEE32.SpecialValues
import Interpreter.Wasm.Examples.FloatNearest

/-!
# Binary32 integral-rounding specifications
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Wasm
open Wasm.FloatNearest

theorem roundIntegral_nan (mode : Wasm.IEEE32.IntegralRounding)
    {a : UInt32} (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.roundIntegral mode a = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.roundIntegral, ha]

theorem roundIntegral_infinity
    (mode : Wasm.IEEE32.IntegralRounding) (negative : Bool) :
    Wasm.IEEE32.roundIntegral mode (Wasm.IEEE32.infinity negative) =
      Wasm.IEEE32.infinity negative := by
  cases mode <;> cases negative <;> decide

theorem roundIntegral_signed_zero
    (mode : Wasm.IEEE32.IntegralRounding) (negative : Bool) :
    Wasm.IEEE32.roundIntegral mode (Wasm.IEEE32.signMask negative) =
      Wasm.IEEE32.signMask negative := by
  cases mode <;> cases negative <;> decide

theorem roundIntegral_finite_nonzero (mode : Wasm.IEEE32.IntegralRounding)
    (a : UInt32) (ha : Finite a)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0) :
    Wasm.IEEE32.roundIntegral mode a =
      Wasm.IEEE32.roundIntegralFinite mode (Wasm.IEEE32.sign a)
        (Wasm.IEEE32.scaledMagnitude a) := by
  have hna := not_nan_of_finite ha
  have hia := not_infinite_of_finite ha
  simp [Wasm.IEEE32.roundIntegral, hna, hia, ha0]

theorem nearest_program_exact (a : UInt32) :
    SmallStep.TerminatesWith (nearestConfig a)
      (fun values _ => values = [.f32 (Wasm.IEEE32.nearest a)]) :=
  nearest_terminates a

theorem nearest_ties_examples :
    Wasm.IEEE32.nearest 0x3FC00000 = 0x40000000 ∧
    Wasm.IEEE32.nearest 0x40200000 = 0x40000000 ∧
    Wasm.IEEE32.nearest 0xBF000000 = 0x80000000 := by
  decide

theorem directional_rounding_examples :
    Wasm.IEEE32.ceil 0xBF400000 = 0x80000000 ∧
    Wasm.IEEE32.floor 0xBF400000 = 0xBF800000 ∧
    Wasm.IEEE32.trunc 0xBFC00000 = 0xBF800000 := by
  decide

#print axioms roundIntegral_finite_nonzero
#print axioms roundIntegral_infinity
#print axioms nearest_program_exact
#print axioms nearest_ties_examples

end CodeLib.IEEE32
