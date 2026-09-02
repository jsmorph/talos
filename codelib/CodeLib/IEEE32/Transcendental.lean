import CodeLib.IEEE32.Division
import CodeLib.IEEE32.Multiplication
import CodeLib.Numerical.ErrorComposition
import Interpreter.Wasm.Examples.FloatSinPolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Algorithm-level transcendental verification

The executable is a cubic small-angle sine approximation built from verified
core operations.  The arbitrary-input theorem identifies its exact rounded
polynomial result.  The interval theorem combines the real cubic Taylor
remainder with the accumulated error of two binary32 multiplications, one
division, and one subtraction.
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

/-- Fixed end-to-end tolerance for the cubic algorithm on `|x| ≤ 1/2`. -/
noncomputable def sineIntervalEpsilon : ℝ := 1 / (2 : ℝ) ^ 11

/-- The real cubic polynomial approximates sine uniformly on the selected
nontrivial interval. -/
theorem cubic_sine_approximation_error (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |(x - x ^ 3 / 6) - Real.sin x| ≤ 1 / 3200 := by
  have hTaylor := Real.sin_bound (x := x) (hx.trans (by norm_num))
  rw [abs_sub_comm] at hTaylor
  calc
    |(x - x ^ 3 / 6) - Real.sin x| ≤ |x| ^ 5 / 100 := hTaylor
    _ ≤ (1 / 2 : ℝ) ^ 5 / 100 := by gcongr
    _ = 1 / 3200 := by norm_num

/-- The rounded binary32 polynomial result is finite and stays within
`2^-11` of real sine for every finite input in `[-1/2, 1/2]`. -/
theorem sinResult_interval_error (x : UInt32) (hx : Finite x)
    (hxBound : |value x| ≤ 1 / 2) :
    Finite (sinResult x) ∧
      |value (sinResult x) - Real.sin (value x)| < sineIntervalEpsilon := by
  let x2 := Wasm.IEEE32.mul x x
  let x3 := Wasm.IEEE32.mul x2 x
  let quotient := Wasm.IEEE32.div x3 six
  let result := Wasm.IEEE32.sub x quotient
  let u : ℝ := 1 / (2 : ℝ) ^ 23
  have hxOne : |value x| ≤ 1 := hxBound.trans (by norm_num)
  have hx2Result := mul_real_error x x hx hx hxOne hxOne
  change Finite x2 ∧
    |value x2 - value x * value x| ≤ multiplicationEpsilon at hx2Result
  have hxxBound : |value x * value x| ≤ 1 / 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (value x)]
  have hx2Bound : |value x2| ≤ 1 := by
    rw [show value x2 =
      (value x2 - value x * value x) + value x * value x by ring]
    calc
      |(value x2 - value x * value x) + value x * value x| ≤
          |value x2 - value x * value x| + |value x * value x| :=
        abs_add_le _ _
      _ ≤ multiplicationEpsilon + 1 / 4 :=
        add_le_add hx2Result.2 hxxBound
      _ ≤ 1 := by norm_num [multiplicationEpsilon]
  have hx3Result :=
    mul_real_error x2 x hx2Result.1 hx hx2Bound hxOne
  change Finite x3 ∧
    |value x3 - value x2 * value x| ≤ multiplicationEpsilon at hx3Result
  have hx2xBound : |value x2 * value x| ≤ 1 / 2 := by
    rw [abs_mul]
    calc
      |value x2| * |value x| ≤ 1 * |value x| :=
        mul_le_mul_of_nonneg_right hx2Bound (abs_nonneg _)
      _ ≤ 1 * (1 / 2) :=
        mul_le_mul_of_nonneg_left hxBound (by norm_num)
      _ = 1 / 2 := by ring
  have hx3Bound : |value x3| ≤ 1 := by
    rw [show value x3 =
      (value x3 - value x2 * value x) + value x2 * value x by ring]
    calc
      |(value x3 - value x2 * value x) + value x2 * value x| ≤
          |value x3 - value x2 * value x| + |value x2 * value x| :=
        abs_add_le _ _
      _ ≤ multiplicationEpsilon + 1 / 2 :=
        add_le_add hx3Result.2 hx2xBound
      _ ≤ 1 := by norm_num [multiplicationEpsilon]
  have hsixFinite : Finite six := by
    norm_num [Finite, six, Wasm.IEEE32.isFinite, Wasm.IEEE32.exponent,
      UInt32.toNat_ofNat]
  have hsixNonzero : Wasm.IEEE32.scaledMagnitude six ≠ 0 := by decide
  have hx3Scaled := scaled_abs_le_of_value_abs_le x3 hx3Bound
  have hx3Magnitude : Wasm.IEEE32.scaledMagnitude x3 ≤ 2 ^ 149 := by
    rw [← natAbs_scaledValue]
    rw [Int.abs_eq_natAbs] at hx3Scaled
    exact_mod_cast hx3Scaled
  have hsixMagnitude : 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude six := by
    decide
  have hquotientResult := div_real_error x3 six hx3Result.1 hsixFinite
    hsixNonzero (hx3Magnitude.trans hsixMagnitude)
  change Finite quotient ∧
    |value quotient - value x3 / value six| ≤ divisionEpsilon at hquotientResult
  have hsixValue : value six = 6 := by
    norm_num [value, six, Wasm.IEEE32.scaledValue,
      Wasm.IEEE32.scaledMagnitude, Wasm.IEEE32.sign,
      Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
  have hx3DivBound : |value x3 / value six| ≤ 1 / 6 := by
    rw [hsixValue, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact div_le_div_of_nonneg_right hx3Bound (by norm_num)
  have hquotientBound : |value quotient| ≤ 1 := by
    rw [show value quotient =
      (value quotient - value x3 / value six) + value x3 / value six by ring]
    calc
      |(value quotient - value x3 / value six) + value x3 / value six| ≤
          |value quotient - value x3 / value six| +
            |value x3 / value six| := abs_add_le _ _
      _ ≤ divisionEpsilon + 1 / 6 :=
        add_le_add hquotientResult.2 hx3DivBound
      _ ≤ 1 := by norm_num [divisionEpsilon]
  have hresult := sub_real_error x quotient hx hquotientResult.1
    hxOne hquotientBound
  change Finite result ∧
    |value result - (value x - value quotient)| ≤ arithmeticEpsilon at hresult
  have hx2Error :
      |value x2 - value x * value x| ≤ u := by
    simpa [u, multiplicationEpsilon] using hx2Result.2
  have hx3Error :
      |value x3 - value x2 * value x| ≤ u := by
    simpa [u, multiplicationEpsilon] using hx3Result.2
  have hquotientError :
      |value quotient - value x3 / 6| ≤ u := by
    rw [← hsixValue]
    simpa [u, divisionEpsilon] using hquotientResult.2
  have hresultError :
      |value result - (value x - value quotient)| ≤ u := by
    simpa [u, arithmeticEpsilon] using hresult.2
  have hx3CubicError :
      |value x3 - value x ^ 3| ≤ 2 * u := by
    have h := CodeLib.Numerical.horner_two_step
      (x := value x) (a := value x) (b := 0) (c := 0)
      (r₁ := value x2) (r₂ := value x3)
      (e₁ := u) (e₂ := u) (M := 1)
      hxOne (by simpa using hx2Error) (by simpa using hx3Error)
    convert h using 1 <;> ring
  have hx3DivCubicError :
      |value x3 / 6 - value x ^ 3 / 6| ≤ (2 * u) / 6 := by
    have h := CodeLib.Numerical.division_by_exact_constant
      (x := value x3) (x₀ := value x ^ 3) (c := (6 : ℝ))
      (e := 2 * u) (by norm_num) hx3CubicError
    simpa using h
  have hquotientCubicError :
      |value quotient - value x ^ 3 / 6| ≤ 2 * u := by
    have hsecond :
        |(0 : ℝ) - (value x ^ 3 / 6 - value x3 / 6)| ≤
          (2 * u) / 6 := by
      rw [show (0 : ℝ) - (value x ^ 3 / 6 - value x3 / 6) =
        value x3 / 6 - value x ^ 3 / 6 by ring]
      exact hx3DivCubicError
    have hsum := CodeLib.Numerical.sum_perturbations
      (x := value quotient) (x₀ := value x3 / 6)
      (y := 0) (y₀ := value x ^ 3 / 6 - value x3 / 6)
      hquotientError hsecond
    calc
      |value quotient - value x ^ 3 / 6| ≤ u + (2 * u) / 6 := by
        convert hsum using 1 <;> ring
      _ ≤ 2 * u := by
        have hu : 0 ≤ u := by positivity
        linarith
  have hroundoff :
      |value result - (value x - value x ^ 3 / 6)| ≤ 3 * u := by
    rw [show value result - (value x - value x ^ 3 / 6) =
      (value result - (value x - value quotient)) +
        (value x ^ 3 / 6 - value quotient) by ring]
    calc
      |(value result - (value x - value quotient)) +
          (value x ^ 3 / 6 - value quotient)| ≤
          |value result - (value x - value quotient)| +
            |value x ^ 3 / 6 - value quotient| := abs_add_le _ _
      _ ≤ u + 2 * u := by
        rw [abs_sub_comm (value x ^ 3 / 6)]
        exact add_le_add hresultError hquotientCubicError
      _ = 3 * u := by ring
  have hTaylor := cubic_sine_approximation_error (value x) hxBound
  change Finite result ∧
    |value result - Real.sin (value x)| < sineIntervalEpsilon
  constructor
  · exact hresult.1
  · rw [show value result - Real.sin (value x) =
      (value result - (value x - value x ^ 3 / 6)) +
        ((value x - value x ^ 3 / 6) - Real.sin (value x)) by ring]
    calc
      |(value result - (value x - value x ^ 3 / 6)) +
          ((value x - value x ^ 3 / 6) - Real.sin (value x))| ≤
          |value result - (value x - value x ^ 3 / 6)| +
            |(value x - value x ^ 3 / 6) - Real.sin (value x)| :=
        abs_add_le _ _
      _ ≤ 3 * u + 1 / 3200 := add_le_add hroundoff hTaylor
      _ < sineIntervalEpsilon := by
        norm_num [u, sineIntervalEpsilon]

/-- Fuel-independent correctness of the decoded WAT sine approximation over
the whole interval `[-1/2, 1/2]`. -/
theorem sin_small_program_interval_error (x : UInt32) (hx : Finite x)
    (hxBound : |value x| ≤ 1 / 2) :
    SmallStep.TerminatesWith (sinConfig x)
      (fun values _ =>
        values = [.f32 (sinResult x)] ∧
          Finite (sinResult x) ∧
          |value (sinResult x) - Real.sin (value x)| <
            sineIntervalEpsilon) := by
  have hresult := sinResult_interval_error x hx hxBound
  exact (sin_terminates x).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

#print axioms sin_small_program_exact
#print axioms sin_small_zero_lt_epsilon
#print axioms sin_half_program_value
#print axioms cubic_sine_approximation_error
#print axioms sinResult_interval_error
#print axioms sin_small_program_interval_error

end CodeLib.IEEE32
