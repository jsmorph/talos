import CodeLib.IEEE32.Roundoff
import Interpreter.Wasm.Examples.FloatSinPolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Algorithm-level transcendental verification

The executable is a cubic small-angle sine approximation built from verified
core operations.  The arbitrary-input theorem identifies its exact rounded
polynomial result.  The first end-to-end analytic theorem uses the fixed input
`x = 0`, where both the polynomial and real sine are exact; extending the
analytic error theorem to a nontrivial interval requires the planned Taylor
remainder and accumulated-roundoff development.
-/

namespace CodeLib.IEEE32

open Wasm
open Wasm.FloatSinPolynomial

theorem sin_small_program_exact (x : UInt32) :
    SmallStep.TerminatesWith (sinConfig x)
      (fun values _ => values = [.f32 (sinResult x)]) :=
  sin_terminates x

/-- End-to-end example: at zero the Wasm result agrees with real sine with
zero error, hence is strictly below the existing fixed epsilon `2^-20`. -/
theorem sin_small_zero_lt_epsilon :
    SmallStep.TerminatesWith (sinConfig 0)
      (fun values _ =>
        values = [.f32 0] ∧ |value 0 - Real.sin 0| < epsilon) := by
  apply SmallStep.TerminatesWith.of_steps (sin_steps 0)
  constructor
  · decide
  · norm_num [value, epsilon, Wasm.IEEE32.scaledValue,
      Wasm.IEEE32.scaledMagnitude, Wasm.IEEE32.sign,
      Wasm.IEEE32.exponent, Wasm.IEEE32.fraction]

theorem sin_half_program_value :
    SmallStep.TerminatesWith (sinConfig 0x3F000000)
      (fun values _ => values = [.f32 0x3EF55555]) := by
  apply SmallStep.TerminatesWith.of_steps (sin_steps 0x3F000000)
  native_decide

#print axioms sin_small_program_exact
#print axioms sin_small_zero_lt_epsilon
#print axioms sin_half_program_value

end CodeLib.IEEE32
