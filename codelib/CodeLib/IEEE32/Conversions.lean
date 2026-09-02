import CodeLib.IEEE32.SpecialValues
import Interpreter.Wasm.Examples.FloatConversion

/-!
# Binary32 conversion specifications
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Wasm
open Wasm.FloatConversion

theorem convert_i32_signed_spec (a : UInt32) :
    Wasm.IEEE32.convertI32S a =
      Wasm.IEEE32.roundScaledMagnitude
        (Wasm.IEEE32.signedI32Value a < 0)
        ((Wasm.IEEE32.signedI32Value a).natAbs * 2 ^ 149) := by
  rfl

theorem convert_i64_unsigned_spec (a : UInt64) :
    Wasm.IEEE32.convertI64U a =
      Wasm.IEEE32.roundScaledMagnitude false (a.toNat * 2 ^ 149) := by
  rfl

theorem truncatedInt_finite (a : UInt32) (ha : Finite a) :
    Wasm.IEEE32.truncatedInt a =
      some (if Wasm.IEEE32.sign a then
        -((Wasm.IEEE32.scaledMagnitude a / 2 ^ 149 : Nat) : Int)
      else (Wasm.IEEE32.scaledMagnitude a / 2 ^ 149 : Nat)) := by
  simp [Wasm.IEEE32.truncatedInt, Finite] at ha ⊢
  exact ha

theorem trunc_nan_and_infinity :
    Wasm.IEEE32.truncI32S Wasm.IEEE32.canonicalNaN = none ∧
    Wasm.IEEE32.truncI32S (Wasm.IEEE32.infinity false) = none ∧
    Wasm.IEEE32.truncI32S (Wasm.IEEE32.infinity true) = none := by
  decide

theorem saturating_nan (a : UInt32)
    (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.truncSatI32S a = 0 ∧
    Wasm.IEEE32.truncSatI32U a = 0 ∧
    Wasm.IEEE32.truncSatI64S a = 0 ∧
    Wasm.IEEE32.truncSatI64U a = 0 := by
  simp [Wasm.IEEE32.truncSatI32S, Wasm.IEEE32.truncSatI32U,
    Wasm.IEEE32.truncSatI64S, Wasm.IEEE32.truncSatI64U, ha]

theorem saturating_infinities :
    Wasm.IEEE32.truncSatI32S (Wasm.IEEE32.infinity false) = 0x7FFFFFFF ∧
    Wasm.IEEE32.truncSatI32S (Wasm.IEEE32.infinity true) = 0x80000000 ∧
    Wasm.IEEE32.truncSatI32U (Wasm.IEEE32.infinity false) = 0xFFFFFFFF ∧
    Wasm.IEEE32.truncSatI32U (Wasm.IEEE32.infinity true) = 0 := by
  decide

theorem signed_i32_conversion_program_exact (a : UInt32) :
    SmallStep.TerminatesWith (convertConfig a)
      (fun values _ => values = [.f32 (Wasm.IEEE32.convertI32S a)]) :=
  convert_terminates a

theorem exact_i32_round_trip_value :
    Wasm.IEEE32.truncI32S (Wasm.IEEE32.convertI32S 0x00FFFFFF) =
      some 0x00FFFFFF := by
  decide

theorem inexact_i32_rounds_to_even :
    Wasm.IEEE32.truncI32S (Wasm.IEEE32.convertI32S 0x01000001) =
      some 0x01000000 := by
  decide

#print axioms convert_i32_signed_spec
#print axioms truncatedInt_finite
#print axioms saturating_nan
#print axioms signed_i32_conversion_program_exact
#print axioms exact_i32_round_trip_value

end CodeLib.IEEE32
