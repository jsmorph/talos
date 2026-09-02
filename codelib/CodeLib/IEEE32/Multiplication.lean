import CodeLib.IEEE32.SpecialValues
import Interpreter.Wasm.Examples.FloatMultiplication

/-!
# Binary32 multiplication specifications

These theorems expose the exact dyadic product used by the interpreter and
connect it to the fuel-independent execution theorem for the example WAT
module.  Exceptional-value theorems cover NaN, infinity, zero, overflow, and
gradual-underflow representatives.
-/

namespace CodeLib.IEEE32

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Wasm
open Wasm.FloatMultiplication

theorem mul_nan_left {a : UInt32} (b : UInt32)
    (ha : Wasm.IEEE32.isNaN a = true) :
    Wasm.IEEE32.mul a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.mul, ha]

theorem mul_nan_right (a : UInt32) {b : UInt32}
    (hb : Wasm.IEEE32.isNaN b = true) :
    Wasm.IEEE32.mul a b = Wasm.IEEE32.canonicalNaN := by
  simp [Wasm.IEEE32.mul, hb]

/-- Multiplying infinity by either signed zero is invalid. -/
theorem mul_infinity_zero (infinitySign zeroSign : Bool) :
    Wasm.IEEE32.mul (Wasm.IEEE32.infinity infinitySign)
        (Wasm.IEEE32.signMask zeroSign) =
      Wasm.IEEE32.canonicalNaN := by
  cases infinitySign <;> cases zeroSign <;> decide

theorem mul_zero_infinity (zeroSign infinitySign : Bool) :
    Wasm.IEEE32.mul (Wasm.IEEE32.signMask zeroSign)
        (Wasm.IEEE32.infinity infinitySign) =
      Wasm.IEEE32.canonicalNaN := by
  cases zeroSign <;> cases infinitySign <;> decide

/-- Infinity signs combine by exclusive-or. -/
theorem mul_infinities (aSign bSign : Bool) :
    Wasm.IEEE32.mul (Wasm.IEEE32.infinity aSign)
        (Wasm.IEEE32.infinity bSign) =
      Wasm.IEEE32.infinity (aSign != bSign) := by
  cases aSign <;> cases bSign <;> decide

/-- For finite, nonzero operands the interpreter forms the exact product of
the two integer magnitudes and performs one dyadic ties-to-even rounding step.
This is the central operation-level multiplication specification. -/
theorem mul_finite_nonzero (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    Wasm.IEEE32.mul a b =
      Wasm.IEEE32.roundDyadicMagnitude
        (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
        (Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b) 149 := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  simp [Wasm.IEEE32.mul, hna, hnb, hia, hib, ha0, hb0]

/-- The decoded WAT program terminates with the exact one-rounding dyadic
product for every pair of finite, nonzero inputs. -/
theorem mul_program_terminates_finite_nonzero (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    SmallStep.TerminatesWith (mulConfig a b)
      (fun values _ =>
        values = [.f32
          (Wasm.IEEE32.roundDyadicMagnitude
            (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
            (Wasm.IEEE32.scaledMagnitude a *
              Wasm.IEEE32.scaledMagnitude b) 149)]) := by
  simpa [mul_finite_nonzero a b ha hb ha0 hb0] using mul_terminates a b

/-- A representative finite overflow: doubling the largest finite binary32
value returns positive infinity. -/
theorem mul_largest_finite_by_two_overflows :
    Wasm.IEEE32.mul 0x7F7FFFFF 0x40000000 =
      Wasm.IEEE32.infinity false := by
  decide

/-- A representative gradual-underflow result at the normal/subnormal
boundary. -/
theorem mul_min_normal_by_half_is_subnormal :
    Wasm.IEEE32.mul 0x00800000 0x3F000000 = 0x00400000 := by
  decide

/-- At exactly half the least-subnormal magnitude, ties-to-even returns the
correctly signed zero. -/
theorem mul_least_subnormal_underflow_tie :
    Wasm.IEEE32.mul 0x00000001 0x3F000000 = 0x00000000 ∧
    Wasm.IEEE32.mul 0x80000001 0x3F000000 = 0x80000000 := by
  decide

#print axioms mul_finite_nonzero
#print axioms mul_program_terminates_finite_nonzero
#print axioms mul_infinities
#print axioms mul_largest_finite_by_two_overflows

end CodeLib.IEEE32
