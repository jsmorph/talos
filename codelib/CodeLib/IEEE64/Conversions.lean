import CodeLib.IEEE64.Operations
import Interpreter.Wasm.Examples.FloatOps

/-!
# Proof-visible binary64 integer conversions

The interpreter's `i32`/`i64` to `f64`, trapping `f64` to integer, and
saturating `f64` to integer instructions now reduce to integer arithmetic in
Lean.  Native `Float` conversion remains only in the differential test suite.
-/

namespace CodeLib.IEEE64

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

open Wasm

theorem convert_i32_signed_spec (a : UInt32) :
    Wasm.IEEE64.convertI32S a =
      Wasm.IEEE64.roundScaledMagnitude
        (Wasm.IEEE64.signedI32Value a < 0)
        ((Wasm.IEEE64.signedI32Value a).natAbs * 2 ^ 1074) := by
  rfl

theorem convert_i64_unsigned_spec (a : UInt64) :
    Wasm.IEEE64.convertI64U a =
      Wasm.IEEE64.roundScaledMagnitude false (a.toNat * 2 ^ 1074) := by
  rfl

theorem truncatedInt_finite (a : UInt64) (ha : Finite a) :
    Wasm.IEEE64.truncatedInt a =
      some (if Wasm.IEEE64.sign a then
        -((Wasm.IEEE64.scaledMagnitude a / 2 ^ 1074 : Nat) : Int)
      else (Wasm.IEEE64.scaledMagnitude a / 2 ^ 1074 : Nat)) := by
  simp [Wasm.IEEE64.truncatedInt, Finite] at ha ⊢
  exact ha

theorem trunc_nan_and_infinity :
    Wasm.IEEE64.truncI32S Wasm.IEEE64.canonicalNaN = none ∧
    Wasm.IEEE64.truncI32S (Wasm.IEEE64.infinity false) = none ∧
    Wasm.IEEE64.truncI32S (Wasm.IEEE64.infinity true) = none := by
  decide

theorem saturating_nan (a : UInt64)
    (ha : Wasm.IEEE64.isNaN a = true) :
    Wasm.IEEE64.truncSatI32S a = 0 ∧
    Wasm.IEEE64.truncSatI32U a = 0 ∧
    Wasm.IEEE64.truncSatI64S a = 0 ∧
    Wasm.IEEE64.truncSatI64U a = 0 := by
  simp [Wasm.IEEE64.truncSatI32S, Wasm.IEEE64.truncSatI32U,
    Wasm.IEEE64.truncSatI64S, Wasm.IEEE64.truncSatI64U, ha]

theorem saturating_infinities :
    Wasm.IEEE64.truncSatI32S (Wasm.IEEE64.infinity false) = 0x7FFFFFFF ∧
    Wasm.IEEE64.truncSatI32S (Wasm.IEEE64.infinity true) = 0x80000000 ∧
    Wasm.IEEE64.truncSatI64U (Wasm.IEEE64.infinity false) =
      0xFFFFFFFFFFFFFFFF ∧
    Wasm.IEEE64.truncSatI64U (Wasm.IEEE64.infinity true) = 0 := by
  decide

/-- The existing example program now exercises only proof-visible conversion
semantics: signed `i32 7` is converted to binary64 and truncated back. -/
theorem signed_i32_roundtrip_program :
    SmallStep.TerminatesWith (Wasm.floatConfig 5)
      (fun values _ => values = [.i32 7]) :=
  Wasm.conv_roundtrip_terminates

theorem exact_i32_round_trip :
    Wasm.IEEE64.truncI32S (Wasm.IEEE64.convertI32S 0x7FFFFFFF) =
      some 0x7FFFFFFF := by
  decide

theorem inexact_i64_rounds_to_even :
    Wasm.IEEE64.convertI64U 0x0020000000000001 =
      0x4340000000000000 := by
  decide

#print axioms convert_i32_signed_spec
#print axioms truncatedInt_finite
#print axioms saturating_nan
#print axioms signed_i32_roundtrip_program
#print axioms inexact_i64_rounds_to_even

end CodeLib.IEEE64
