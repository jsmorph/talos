import CodeLib.IEEE32.SpecialValues
import Interpreter.Wasm.Examples.FloatSquareRoot

/-!
# Binary32 square-root specifications
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Wasm
open Wasm.FloatSquareRoot

theorem sqrt_nan {a : UInt32} (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.sqrt a = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.sqrt, ha]

theorem sqrt_signed_zero (negative : Bool) :
    Wasm.IEEE32.sqrt (Wasm.IEEE32.signMask negative) =
      Wasm.IEEE32.signMask negative := by
  cases negative <;> decide

theorem sqrt_positive_infinity :
    Wasm.IEEE32.sqrt (Wasm.IEEE32.infinity false) =
      Wasm.IEEE32.infinity false := by
  decide

theorem sqrt_negative_infinity :
    Wasm.IEEE32.sqrt (Wasm.IEEE32.infinity true) =
      Wasm.IEEE32.canonicalNaN := by
  decide

/-- Every positive, finite input is passed to the exact integer-square-root
rounder applied to `scaledMagnitude * 2^149`. -/
theorem sqrt_positive_finite (a : UInt32)
    (ha : Finite a)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE32.sign a = false) :
    Wasm.IEEE32.sqrt a =
      Wasm.IEEE32.roundSqrtMagnitude (Wasm.IEEE32.scaledMagnitude a) := by
  have hna := not_nan_of_finite ha
  have hia := not_infinite_of_finite ha
  simp [Wasm.IEEE32.sqrt, hna, hia, ha0, hsign]

theorem sqrt_program_terminates_positive_finite (a : UInt32)
    (ha : Finite a)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE32.sign a = false) :
    SmallStep.TerminatesWith (sqrtConfig a)
      (fun values _ =>
        values = [.f32
          (Wasm.IEEE32.roundSqrtMagnitude
            (Wasm.IEEE32.scaledMagnitude a))]) := by
  simpa [sqrt_positive_finite a ha ha0 hsign] using sqrt_terminates a

theorem sqrt_four_exact : Wasm.IEEE32.sqrt 0x40800000 = 0x40000000 := by
  native_decide

theorem sqrt_two_rounded :
    Wasm.IEEE32.sqrt 0x40000000 = 0x3FB504F3 := by
  native_decide

theorem sqrt_least_subnormal_rounded :
    Wasm.IEEE32.sqrt 0x00000001 = 0x1A3504F3 := by
  native_decide

#print axioms sqrt_positive_finite
#print axioms sqrt_program_terminates_positive_finite
#print axioms sqrt_negative_infinity
#print axioms sqrt_two_rounded

end CodeLib.IEEE32
