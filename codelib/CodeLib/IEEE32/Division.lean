import CodeLib.IEEE32.SpecialValues
import Interpreter.Wasm.Examples.FloatDivision

/-!
# Binary32 division specifications
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Wasm
open Wasm.FloatDivision

theorem div_nan_left {a : UInt32} (b : UInt32)
    (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.div a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.div, ha]

theorem div_nan_right (a : UInt32) {b : UInt32}
    (hb : Wasm.IEEE32.isNaN b = true) :
    Wasm.IEEE32.div a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.div, hb]

theorem div_infinities (aSign bSign : Bool) :
    Wasm.IEEE32.div (Wasm.IEEE32.infinity aSign)
        (Wasm.IEEE32.infinity bSign) =
      Wasm.IEEE32.canonicalNaN := by
  cases aSign <;> cases bSign <;> decide

theorem div_zero_zero (aSign bSign : Bool) :
    Wasm.IEEE32.div (Wasm.IEEE32.signMask aSign)
        (Wasm.IEEE32.signMask bSign) =
      Wasm.IEEE32.canonicalNaN := by
  cases aSign <;> cases bSign <;> decide

theorem div_one_zero (numeratorSign denominatorSign : Bool) :
    Wasm.IEEE32.div
        (Wasm.IEEE32.encodeFinite numeratorSign 127 0)
        (Wasm.IEEE32.signMask denominatorSign) =
      Wasm.IEEE32.infinity (numeratorSign != denominatorSign) := by
  cases numeratorSign <;> cases denominatorSign <;> decide

/-- A finite, nonzero quotient is rounded once from its exact rational value.
The numerator's factor `2^149` converts the quotient back to the common scaled
unit before quotient/remainder rounding. -/
theorem div_finite_nonzero (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    Wasm.IEEE32.div a b =
      Wasm.IEEE32.roundRationalMagnitude
        (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
        (Wasm.IEEE32.scaledMagnitude a * 2 ^ 149)
        (Wasm.IEEE32.scaledMagnitude b) := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  simp [Wasm.IEEE32.div, hna, hnb, hia, hib, ha0, hb0]

theorem div_program_terminates_finite_nonzero (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    SmallStep.TerminatesWith (divConfig a b)
      (fun values _ =>
        values = [.f32
          (Wasm.IEEE32.roundRationalMagnitude
            (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
            (Wasm.IEEE32.scaledMagnitude a * 2 ^ 149)
            (Wasm.IEEE32.scaledMagnitude b))]) := by
  simpa [div_finite_nonzero a b ha hb ha0 hb0] using div_terminates a b

theorem div_min_normal_by_two_is_subnormal :
    Wasm.IEEE32.div 0x00800000 0x40000000 = 0x00400000 := by
  decide

theorem div_positive_overflow :
    Wasm.IEEE32.div 0x7F7FFFFF 0x3F000000 =
      Wasm.IEEE32.infinity false := by
  decide

theorem div_least_subnormal_by_two_underflows :
    Wasm.IEEE32.div 0x00000001 0x40000000 = 0x00000000 := by
  decide

#print axioms div_finite_nonzero
#print axioms div_program_terminates_finite_nonzero
#print axioms div_infinities
#print axioms div_positive_overflow

end CodeLib.IEEE32
