import CodeLib.IEEE64.Rounders
import Interpreter.Wasm.Examples.Float64AddSub
import Interpreter.Wasm.Examples.Float64Division
import Interpreter.Wasm.Examples.Float64Multiplication
import Interpreter.Wasm.Examples.Float64SquareRoot
import Interpreter.Wasm.Examples.IEEE64
import Mathlib.Tactic

/-!
# Binary64 operation specifications
-/

namespace CodeLib.IEEE64

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

open Wasm
open Wasm.Float64Addition
open Wasm.Float64Division
open Wasm.Float64Multiplication
open Wasm.Float64SquareRoot
open Wasm.Float64Subtraction

theorem add_program_real_error (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    SmallStep.TerminatesWith (addConfig a b)
      (fun values _ =>
        values = [.f64 (Wasm.IEEE64.add a b)] ∧
          Finite (Wasm.IEEE64.add a b) ∧
          |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
            arithmeticEpsilon) := by
  have hresult := add_real_error a b ha hb haBound hbBound
  exact (add_terminates a b).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

theorem sub_program_real_error (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    SmallStep.TerminatesWith (subConfig a b)
      (fun values _ =>
        values = [.f64 (Wasm.IEEE64.sub a b)] ∧
          Finite (Wasm.IEEE64.sub a b) ∧
          |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤
            arithmeticEpsilon) := by
  have hresult := sub_real_error a b ha hb haBound hbBound
  exact (sub_terminates a b).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

theorem mul_nan_left {a : UInt64} (b : UInt64)
    (ha : Wasm.IEEE64.isNaN a = true) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.canonicalNaN := by
  simp [Wasm.IEEE64.mul, ha]

theorem mul_infinities (aSign bSign : Bool) :
    Wasm.IEEE64.mul (Wasm.IEEE64.infinity aSign)
        (Wasm.IEEE64.infinity bSign) =
      Wasm.IEEE64.infinity (aSign != bSign) := by
  cases aSign <;> cases bSign <;> decide

theorem mul_finite_rounder (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul a b =
      Wasm.IEEE64.roundDyadicMagnitude
        (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
        (Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b)
        1074 := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  by_cases ha0 : Wasm.IEEE64.scaledMagnitude a = 0 <;>
    by_cases hb0 : Wasm.IEEE64.scaledMagnitude b = 0 <;>
    simp [Wasm.IEEE64.mul, hna, hnb, hia, hib, ha0, hb0,
      Wasm.IEEE64.roundDyadicMagnitude]

noncomputable def multiplicationEpsilon : ℝ := 1 / (2 : ℝ) ^ 52

theorem mul_real_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    Finite (Wasm.IEEE64.mul a b) ∧
      |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
        multiplicationEpsilon := by
  have haScaled := scaled_abs_le_of_value_abs_le a haBound
  have hbScaled := scaled_abs_le_of_value_abs_le b hbBound
  have haMag : Wasm.IEEE64.scaledMagnitude a ≤ 2 ^ 1074 := by
    rw [Int.abs_eq_natAbs, natAbs_scaledValue] at haScaled
    exact_mod_cast haScaled
  have hbMag : Wasm.IEEE64.scaledMagnitude b ≤ 2 ^ 1074 := by
    rw [Int.abs_eq_natAbs, natAbs_scaledValue] at hbScaled
    exact_mod_cast hbScaled
  let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
  have hn : n < 2 ^ 2149 := by
    calc
      n ≤ 2 ^ 1074 * 2 ^ 1074 := Nat.mul_le_mul haMag hbMag
      _ = 2 ^ 2148 := by rw [← pow_add]
      _ < 2 ^ 2149 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hs := roundDyadicMagnitude1074_spec
    (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n hn
  have hmul := mul_finite_rounder a b ha hb
  rw [hmul]
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE64.scaledValue
          (Wasm.IEEE64.roundDyadicMagnitude
            (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n 1074) *
          (2 : Int) ^ 1074 -
        Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b
    have hz : |z| ≤ (2 ^ 2096 : Nat) := by
      have herr := hs.2.2
      have hresultSign := hs.2.1
      have habs (x y : Int) : |-x + y| = |x + -y| := by
        rw [show -x + y = -(x + -y) by ring, abs_neg]
      cases hsa : Wasm.IEEE64.sign a <;>
        cases hsb : Wasm.IEEE64.sign b <;>
        simp [n, hsa, hsb] at hresultSign <;>
        simp [Wasm.IEEE64.scaledValue, hresultSign, hsa, hsb, n, z]
          at herr ⊢
      all_goals
        first
        | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
        | rw [habs]
          simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
    have heq :
        value (Wasm.IEEE64.roundDyadicMagnitude
            (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n 1074) -
            value a * value b =
          (z : ℝ) / (2 : ℝ) ^ 2148 := by
      simp [value, z]
      field_simp
      ring
    rw [heq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 2148)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 2148)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ 2096 := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ 2096 := hzReal
      _ = multiplicationEpsilon * (2 : ℝ) ^ 2148 := by
        norm_num [multiplicationEpsilon]

/-- Division of finite operands by a finite nonzero denominator is a single
rational rounding of the exact quotient in the common `2^-1074` scale. -/
theorem div_finite_rounder (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    Wasm.IEEE64.div a b =
      Wasm.IEEE64.roundRationalMagnitude
        (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
        (Wasm.IEEE64.scaledMagnitude a * 2 ^ 1074)
        (Wasm.IEEE64.scaledMagnitude b) := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  by_cases ha0 : Wasm.IEEE64.scaledMagnitude a = 0
  · simp [Wasm.IEEE64.div, hna, hnb, hia, hib, ha0, hb0,
      Wasm.IEEE64.roundRationalMagnitude]
  · simp [Wasm.IEEE64.div, hna, hnb, hia, hib, ha0, hb0]

/-- Cleared-denominator integer error when the exact quotient magnitude is at
most one. -/
theorem div_scaled_error (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE64.scaledMagnitude a ≤
      Wasm.IEEE64.scaledMagnitude b) :
    Finite (Wasm.IEEE64.div a b) ∧
      |Wasm.IEEE64.scaledValue (Wasm.IEEE64.div a b) *
          Wasm.IEEE64.scaledValue b -
        Wasm.IEEE64.scaledValue a * (2 : Int) ^ 1074| ≤
          Wasm.IEEE64.scaledMagnitude b * 2 ^ 1022 := by
  let numerator := Wasm.IEEE64.scaledMagnitude a * 2 ^ 1074
  let denominator := Wasm.IEEE64.scaledMagnitude b
  have hbound : numerator ≤ denominator * 2 ^ 1074 := by
    simp [numerator, denominator]
    exact hab
  have hs := roundRationalMagnitude_spec
    (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
    numerator denominator hb0 hbound
  have hdiv := div_finite_rounder a b ha hb hb0
  rw [hdiv]
  constructor
  · exact hs.1
  · have herr := hs.2.2
    have hresultSign := hs.2.1
    have habs (x y : Int) : |-x + y| = |x + -y| := by
      rw [show -x + y = -(x + -y) by ring, abs_neg]
    cases hsa : Wasm.IEEE64.sign a <;>
      cases hsb : Wasm.IEEE64.sign b <;>
      simp [numerator, denominator, hsa, hsb] at hresultSign <;>
      simp [Wasm.IEEE64.scaledValue, hresultSign, hsa, hsb,
        numerator, denominator] at herr ⊢
    all_goals
      first
      | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
      | rw [habs]
        simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

noncomputable def divisionEpsilon : ℝ := 1 / (2 : ℝ) ^ 52

/-- For finite inputs, a nonzero denominator, and quotient magnitude at most
one, binary64 division has absolute real error at most `2^-52`. -/
theorem div_real_error (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE64.scaledMagnitude a ≤
      Wasm.IEEE64.scaledMagnitude b) :
    Finite (Wasm.IEEE64.div a b) ∧
      |value (Wasm.IEEE64.div a b) - value a / value b| ≤
        divisionEpsilon := by
  have hs := div_scaled_error a b ha hb hb0 hab
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.div a b) *
          Wasm.IEEE64.scaledValue b -
        Wasm.IEEE64.scaledValue a * (2 : Int) ^ 1074
    have hz : |z| ≤ Wasm.IEEE64.scaledMagnitude b * 2 ^ 1022 := hs.2
    have hbScaled : Wasm.IEEE64.scaledValue b ≠ 0 := by
      intro h
      apply hb0
      rw [← natAbs_scaledValue]
      simp [h]
    have hbScaledReal : (Wasm.IEEE64.scaledValue b : ℝ) ≠ 0 := by
      exact_mod_cast hbScaled
    have heq :
        value (Wasm.IEEE64.div a b) - value a / value b =
          (z : ℝ) /
            ((2 : ℝ) ^ 1074 * Wasm.IEEE64.scaledValue b) := by
      simp [value, z]
      field_simp
      ring
    have hbAbs :
        |(Wasm.IEEE64.scaledValue b : ℝ)| =
          Wasm.IEEE64.scaledMagnitude b := by
      simp [Wasm.IEEE64.scaledValue]
      split <;> simp
    rw [heq, abs_div]
    have hdenPos :
        0 < |(2 : ℝ) ^ 1074 * Wasm.IEEE64.scaledValue b| := by
      positivity
    apply (div_le_iff₀ hdenPos).2
    have hzReal :
        |(z : ℝ)| ≤
          (Wasm.IEEE64.scaledMagnitude b : ℝ) * 2 ^ 1022 := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤
          (Wasm.IEEE64.scaledMagnitude b : ℝ) * 2 ^ 1022 := hzReal
      _ = divisionEpsilon *
          |(2 : ℝ) ^ 1074 * Wasm.IEEE64.scaledValue b| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 1074),
          hbAbs]
        norm_num [divisionEpsilon]
        ring

theorem div_program_exact (a b : UInt64) :
    SmallStep.TerminatesWith (divConfig a b)
      (fun values _ => values = [.f64 (Wasm.IEEE64.div a b)]) :=
  div_terminates a b

/-- Fuel-independent correctness of decoded `f64.div`, including finiteness
and its absolute real-error contract. -/
theorem div_program_real_error (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE64.scaledMagnitude a ≤
      Wasm.IEEE64.scaledMagnitude b) :
    SmallStep.TerminatesWith (divConfig a b)
      (fun values _ =>
        values = [.f64 (Wasm.IEEE64.div a b)] ∧
          Finite (Wasm.IEEE64.div a b) ∧
          |value (Wasm.IEEE64.div a b) - value a / value b| ≤
            divisionEpsilon) := by
  have hresult := div_real_error a b ha hb hb0 hab
  exact (div_terminates a b).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

/-- Every positive, nonzero finite input reaches the exact integer-square-root
rounder. -/
theorem sqrt_positive_finite (a : UInt64)
    (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE64.sign a = false) :
    Wasm.IEEE64.sqrt a =
      Wasm.IEEE64.roundSqrtMagnitude (Wasm.IEEE64.scaledMagnitude a) := by
  have hna := not_nan_of_finite ha
  have hia := not_infinite_of_finite ha
  simp [Wasm.IEEE64.sqrt, hna, hia, ha0, hsign]

noncomputable def squareRootEpsilon : ℝ := 1 / (2 : ℝ) ^ 52

/-- On positive finite binary64 inputs no larger than one, square root differs
from exact real square root by at most `2^-52`. -/
theorem sqrt_real_error (a : UInt64)
    (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE64.sign a = false)
    (hbound : Wasm.IEEE64.scaledMagnitude a ≤ 2 ^ 1074) :
    Finite (Wasm.IEEE64.sqrt a) ∧
      |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| ≤
        squareRootEpsilon := by
  let magnitude := Wasm.IEEE64.scaledMagnitude a
  let result := Wasm.IEEE64.roundSqrtMagnitude magnitude
  have hs := roundSqrtMagnitude_spec magnitude hbound
  have hsqrt := sqrt_positive_finite a ha ha0 hsign
  rw [hsqrt]
  constructor
  · exact hs.1
  · have hscalePos : 0 < (2 : ℝ) ^ 1074 := by positivity
    have hmagnitudeNonnegative : 0 ≤ (magnitude : ℝ) := by positivity
    have hsqrtScalePos : 0 < Real.sqrt ((2 : ℝ) ^ 1074) :=
      Real.sqrt_pos.2 hscalePos
    have hsqrtScaleSq :
        Real.sqrt ((2 : ℝ) ^ 1074) * Real.sqrt ((2 : ℝ) ^ 1074) =
          (2 : ℝ) ^ 1074 := by
      simpa [pow_two] using Real.sq_sqrt (le_of_lt hscalePos)
    have hsqrtScale :
        Real.sqrt ((magnitude : ℝ) / (2 : ℝ) ^ 1074) =
          Real.sqrt ((magnitude : ℝ) * (2 : ℝ) ^ 1074) /
            (2 : ℝ) ^ 1074 := by
      rw [Real.sqrt_div hmagnitudeNonnegative,
        Real.sqrt_mul hmagnitudeNonnegative]
      calc
        Real.sqrt (magnitude : ℝ) / Real.sqrt ((2 : ℝ) ^ 1074) =
            Real.sqrt (magnitude : ℝ) * Real.sqrt ((2 : ℝ) ^ 1074) /
              (Real.sqrt ((2 : ℝ) ^ 1074) *
                Real.sqrt ((2 : ℝ) ^ 1074)) := by
          field_simp [ne_of_gt hsqrtScalePos]
        _ = Real.sqrt (magnitude : ℝ) * Real.sqrt ((2 : ℝ) ^ 1074) /
              (2 : ℝ) ^ 1074 := by rw [hsqrtScaleSq]
    have hvalueA :
        value a = (magnitude : ℝ) / (2 : ℝ) ^ 1074 := by
      simp [value, magnitude, Wasm.IEEE64.scaledValue, hsign]
    have hvalueResult :
        value result =
          (Wasm.IEEE64.scaledMagnitude result : ℝ) / (2 : ℝ) ^ 1074 := by
      simp [value, Wasm.IEEE64.scaledValue, hs.2.1, result]
    have heq :
        value result - Real.sqrt (value a) =
          ((Wasm.IEEE64.scaledMagnitude result : ℝ) -
              Real.sqrt ((magnitude : ℝ) * (2 : ℝ) ^ 1074)) /
            (2 : ℝ) ^ 1074 := by
      rw [hvalueA, hvalueResult, hsqrtScale]
      ring
    change |value result - Real.sqrt (value a)| ≤ squareRootEpsilon
    rw [heq, abs_div, abs_of_pos hscalePos]
    apply (div_le_iff₀ hscalePos).2
    have herr := hs.2.2
    calc
      |(Wasm.IEEE64.scaledMagnitude result : ℝ) -
          Real.sqrt ((magnitude : ℝ) * (2 : ℝ) ^ 1074)| ≤
          (2 : ℝ) ^ 1022 := by
        simpa only [result, magnitude, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using herr
      _ = squareRootEpsilon * (2 : ℝ) ^ 1074 := by
        norm_num [squareRootEpsilon]

theorem sqrt_program_exact (a : UInt64) :
    SmallStep.TerminatesWith (sqrtConfig a)
      (fun values _ => values = [.f64 (Wasm.IEEE64.sqrt a)]) :=
  sqrt_terminates a

/-- Fuel-independent correctness of decoded `f64.sqrt`, including finiteness
and the `2^-52` real-error bound. -/
theorem sqrt_program_real_error (a : UInt64)
    (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE64.sign a = false)
    (hbound : Wasm.IEEE64.scaledMagnitude a ≤ 2 ^ 1074) :
    SmallStep.TerminatesWith (sqrtConfig a)
      (fun values _ =>
        values = [.f64 (Wasm.IEEE64.sqrt a)] ∧
          Finite (Wasm.IEEE64.sqrt a) ∧
          |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| ≤
            squareRootEpsilon) := by
  have hresult := sqrt_real_error a ha ha0 hsign hbound
  exact (sqrt_terminates a).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

theorem sqrt_special_values :
    Wasm.IEEE64.sqrt 0x8000000000000000 = 0x8000000000000000 ∧
    Wasm.IEEE64.sqrt 0x7FF0000000000000 = 0x7FF0000000000000 ∧
    Wasm.IEEE64.sqrt 0xBFF0000000000000 = Wasm.IEEE64.canonicalNaN := by
  decide

theorem mul_program_exact (a b : UInt64) :
    SmallStep.TerminatesWith (mulConfig a b)
      (fun values _ => values = [.f64 (Wasm.IEEE64.mul a b)]) :=
  mul_terminates a b

theorem mul_program_real_error (a b : UInt64)
    (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    SmallStep.TerminatesWith (mulConfig a b)
      (fun values _ =>
        values = [.f64 (Wasm.IEEE64.mul a b)] ∧
          Finite (Wasm.IEEE64.mul a b) ∧
          |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
            multiplicationEpsilon) := by
  have hresult := mul_real_error a b ha hb haBound hbBound
  exact (mul_terminates a b).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

theorem arithmetic_examples :
    Wasm.IEEE64.add 0x3FF0000000000000 0x3CA0000000000000 =
      0x3FF0000000000000 ∧
    Wasm.IEEE64.div 0x3FF0000000000000 0 = 0x7FF0000000000000 ∧
    Wasm.IEEE64.sqrt 0x4010000000000000 = 0x4000000000000000 := by
  native_decide

#print axioms mul_nan_left
#print axioms mul_infinities
#print axioms add_program_real_error
#print axioms sub_program_real_error
#print axioms mul_program_exact
#print axioms mul_real_error
#print axioms mul_program_real_error
#print axioms div_finite_rounder
#print axioms div_scaled_error
#print axioms div_real_error
#print axioms div_program_real_error
#print axioms sqrt_positive_finite
#print axioms sqrt_real_error
#print axioms sqrt_program_real_error
#print axioms arithmetic_examples

end CodeLib.IEEE64
