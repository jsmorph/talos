import CodeLib.IEEE32.SpecialValues
import Interpreter.Wasm.Examples.FloatClamp

/-!
# Binary32 comparison, selection, and sign specifications
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Wasm
open Wasm.FloatClamp

theorem eq_finite (a b : UInt32) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE32.eq a b =
      decide (Wasm.IEEE32.scaledValue a = Wasm.IEEE32.scaledValue b) := by
  simp [Wasm.IEEE32.eq, not_nan_of_finite ha, not_nan_of_finite hb,
    beq_eq_decide]

theorem lt_finite (a b : UInt32) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE32.lt a b =
      decide (Wasm.IEEE32.scaledValue a < Wasm.IEEE32.scaledValue b) := by
  simp [Wasm.IEEE32.lt, not_nan_of_finite ha, not_nan_of_finite hb]

theorem le_finite (a b : UInt32) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE32.le a b =
      decide (Wasm.IEEE32.scaledValue a ≤ Wasm.IEEE32.scaledValue b) := by
  simp [Wasm.IEEE32.le, not_nan_of_finite ha, not_nan_of_finite hb]

theorem min_nan_left {a : UInt32} (b : UInt32)
    (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.min a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.min, ha]

theorem max_nan_right (a : UInt32) {b : UInt32}
    (hb : Wasm.IEEE32.isNaN b = true) :
    Wasm.IEEE32.max a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.max, hb]

theorem min_signed_zeros (aSign bSign : Bool) :
    Wasm.IEEE32.min (Wasm.IEEE32.signMask aSign)
        (Wasm.IEEE32.signMask bSign) =
      Wasm.IEEE32.signMask (aSign || bSign) := by
  cases aSign <;> cases bSign <;> decide

theorem max_signed_zeros (aSign bSign : Bool) :
    Wasm.IEEE32.max (Wasm.IEEE32.signMask aSign)
        (Wasm.IEEE32.signMask bSign) =
      Wasm.IEEE32.signMask (aSign && bSign) := by
  cases aSign <;> cases bSign <;> decide

theorem copySign_fields (value source : UInt32) :
    Wasm.IEEE32.copySign value source =
      Wasm.IEEE32.encodeFinite (Wasm.IEEE32.sign source)
        (Wasm.IEEE32.exponent value) (Wasm.IEEE32.fraction value) := by
  rfl

/-- The WAT clamp program has a fuel-independent exact semantics for all bit
patterns; NaN and signed-zero behavior is inherited from the proved `min` and
`max` definitions above. -/
theorem clamp_program_exact (x low high : UInt32) :
    SmallStep.TerminatesWith (clampConfig x low high)
      (fun values _ =>
        values = [.f32
          (Wasm.IEEE32.min (Wasm.IEEE32.max x low) high)]) := by
  simpa [clampResult] using clamp_terminates x low high

#print axioms eq_finite
#print axioms min_signed_zeros
#print axioms copySign_fields
#print axioms clamp_program_exact

end CodeLib.IEEE32
