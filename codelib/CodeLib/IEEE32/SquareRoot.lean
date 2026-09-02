import CodeLib.IEEE32.SpecialValues
import CodeLib.IEEE32.Rounders
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

noncomputable def squareRootEpsilon : ℝ := 1 / (2 : ℝ) ^ 23

/-- On positive finite inputs between zero and one, binary32 square root
differs from the exact real square root by at most `2^-23`. -/
theorem sqrt_real_error (a : UInt32)
    (ha : Finite a)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE32.sign a = false)
    (hbound : Wasm.IEEE32.scaledMagnitude a ≤ 2 ^ 149) :
    Finite (Wasm.IEEE32.sqrt a) ∧
      |value (Wasm.IEEE32.sqrt a) - Real.sqrt (value a)| ≤
        squareRootEpsilon := by
  let magnitude := Wasm.IEEE32.scaledMagnitude a
  let result := Wasm.IEEE32.roundSqrtMagnitude magnitude
  have hs := roundSqrtMagnitude_spec magnitude hbound
  have hsqrt := sqrt_positive_finite a ha ha0 hsign
  rw [hsqrt]
  constructor
  · exact hs.1
  · have hscalePos : 0 < (2 : ℝ) ^ 149 := by positivity
    have hmagnitudeNonnegative : 0 ≤ (magnitude : ℝ) := by positivity
    have hsqrtScalePos : 0 < Real.sqrt ((2 : ℝ) ^ 149) :=
      Real.sqrt_pos.2 hscalePos
    have hsqrtScaleSq :
        Real.sqrt ((2 : ℝ) ^ 149) * Real.sqrt ((2 : ℝ) ^ 149) =
          (2 : ℝ) ^ 149 := by
      simpa [pow_two] using Real.sq_sqrt (le_of_lt hscalePos)
    have hsqrtScale :
        Real.sqrt ((magnitude : ℝ) / (2 : ℝ) ^ 149) =
          Real.sqrt ((magnitude : ℝ) * (2 : ℝ) ^ 149) /
            (2 : ℝ) ^ 149 := by
      rw [Real.sqrt_div hmagnitudeNonnegative,
        Real.sqrt_mul hmagnitudeNonnegative]
      calc
        Real.sqrt (magnitude : ℝ) / Real.sqrt ((2 : ℝ) ^ 149) =
            Real.sqrt (magnitude : ℝ) * Real.sqrt ((2 : ℝ) ^ 149) /
              (Real.sqrt ((2 : ℝ) ^ 149) *
                Real.sqrt ((2 : ℝ) ^ 149)) := by
          field_simp [ne_of_gt hsqrtScalePos]
        _ = Real.sqrt (magnitude : ℝ) * Real.sqrt ((2 : ℝ) ^ 149) /
              (2 : ℝ) ^ 149 := by rw [hsqrtScaleSq]
    have hvalueA :
        value a = (magnitude : ℝ) / (2 : ℝ) ^ 149 := by
      simp [value, magnitude, Wasm.IEEE32.scaledValue, hsign]
    have hvalueResult :
        value result =
          (Wasm.IEEE32.scaledMagnitude result : ℝ) / (2 : ℝ) ^ 149 := by
      simp [value, Wasm.IEEE32.scaledValue, hs.2.1, result]
    have heq :
        value result - Real.sqrt (value a) =
          ((Wasm.IEEE32.scaledMagnitude result : ℝ) -
              Real.sqrt ((magnitude : ℝ) * (2 : ℝ) ^ 149)) /
            (2 : ℝ) ^ 149 := by
      rw [hvalueA, hvalueResult, hsqrtScale]
      ring
    change |value result - Real.sqrt (value a)| ≤ squareRootEpsilon
    rw [heq, abs_div, abs_of_pos hscalePos]
    apply (div_le_iff₀ hscalePos).2
    have herr := hs.2.2
    calc
      |(Wasm.IEEE32.scaledMagnitude result : ℝ) -
          Real.sqrt ((magnitude : ℝ) * (2 : ℝ) ^ 149)| ≤
          (2 : ℝ) ^ 126 := by
        simpa only [result, magnitude, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using herr
      _ = squareRootEpsilon * (2 : ℝ) ^ 149 := by
        norm_num [squareRootEpsilon]

/-- Fuel-independent correctness of the hand-written WAT square-root
program, including the real error contract. -/
theorem sqrt_program_terminates_real_error (a : UInt32)
    (ha : Finite a)
    (ha0 : Wasm.IEEE32.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE32.sign a = false)
    (hbound : Wasm.IEEE32.scaledMagnitude a ≤ 2 ^ 149) :
    SmallStep.TerminatesWith (sqrtConfig a)
      (fun values _ =>
        values = [.f32 (Wasm.IEEE32.sqrt a)] ∧
          Finite (Wasm.IEEE32.sqrt a) ∧
          |value (Wasm.IEEE32.sqrt a) - Real.sqrt (value a)| ≤
            squareRootEpsilon) := by
  have hresult := sqrt_real_error a ha ha0 hsign hbound
  exact (sqrt_terminates a).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

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
#print axioms sqrt_real_error
#print axioms sqrt_program_terminates_real_error
#print axioms sqrt_negative_infinity
#print axioms sqrt_two_rounded

end CodeLib.IEEE32
