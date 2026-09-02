import CodeLib.IEEE32.Rounders
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

/-- The same exact rational-rounding path also covers a zero numerator; only
the finite denominator must be nonzero. -/
theorem div_finite_rounder (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
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
  by_cases ha0 : Wasm.IEEE32.scaledMagnitude a = 0
  · simp [Wasm.IEEE32.div, hna, hnb, hia, hib, ha0, hb0,
      Wasm.IEEE32.roundRationalMagnitude]
  · simp [Wasm.IEEE32.div, hna, hnb, hia, hib, ha0, hb0]

/-- Cleared-denominator error for bounded division.  The magnitude hypothesis
states exactly that the quotient has absolute value at most one. -/
theorem div_scaled_error (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE32.scaledMagnitude a ≤
      Wasm.IEEE32.scaledMagnitude b) :
    Finite (Wasm.IEEE32.div a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.div a b) *
          Wasm.IEEE32.scaledValue b -
        Wasm.IEEE32.scaledValue a * (2 : Int) ^ 149| ≤
          Wasm.IEEE32.scaledMagnitude b * 2 ^ 126 := by
  let numerator := Wasm.IEEE32.scaledMagnitude a * 2 ^ 149
  let denominator := Wasm.IEEE32.scaledMagnitude b
  have hbound : numerator ≤ denominator * 2 ^ 149 := by
    simp [numerator, denominator]
    exact hab
  have hs := roundRationalMagnitude_spec
    (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
    numerator denominator hb0 hbound
  have hdiv := div_finite_rounder a b ha hb hb0
  rw [hdiv]
  constructor
  · exact hs.1
  · have herr := hs.2.2
    have hresultSign := hs.2.1
    have habs (x y : Int) : |-x + y| = |x + -y| := by
      rw [show -x + y = -(x + -y) by ring, abs_neg]
    cases hsa : Wasm.IEEE32.sign a <;>
      cases hsb : Wasm.IEEE32.sign b <;>
      simp [numerator, denominator, hsa, hsb] at hresultSign <;>
      simp [Wasm.IEEE32.scaledValue, hresultSign, hsa, hsb,
        numerator, denominator] at herr ⊢
    all_goals
      first
      | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
      | rw [habs]
        simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

noncomputable def divisionEpsilon : ℝ := 1 / (2 : ℝ) ^ 23

/-- On nonzero finite denominators and quotients of magnitude at most one,
binary32 division differs from exact real division by at most `2^-23`. -/
theorem div_real_error (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE32.scaledMagnitude a ≤
      Wasm.IEEE32.scaledMagnitude b) :
    Finite (Wasm.IEEE32.div a b) ∧
      |value (Wasm.IEEE32.div a b) - value a / value b| ≤
        divisionEpsilon := by
  have hs := div_scaled_error a b ha hb hb0 hab
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.div a b) *
          Wasm.IEEE32.scaledValue b -
        Wasm.IEEE32.scaledValue a * (2 : Int) ^ 149
    have hz : |z| ≤ Wasm.IEEE32.scaledMagnitude b * 2 ^ 126 := hs.2
    have hbScaled : Wasm.IEEE32.scaledValue b ≠ 0 := by
      intro h
      apply hb0
      rw [← natAbs_scaledValue]
      simp [h]
    have hbScaledReal : (Wasm.IEEE32.scaledValue b : ℝ) ≠ 0 := by
      exact_mod_cast hbScaled
    have heq :
        value (Wasm.IEEE32.div a b) - value a / value b =
          (z : ℝ) /
            ((2 : ℝ) ^ 149 * Wasm.IEEE32.scaledValue b) := by
      simp [value, z]
      field_simp
      ring
    have hbAbs :
        |(Wasm.IEEE32.scaledValue b : ℝ)| =
          Wasm.IEEE32.scaledMagnitude b := by
      simp [Wasm.IEEE32.scaledValue]
      split <;> simp
    rw [heq, abs_div]
    have hdenPos :
        0 < |(2 : ℝ) ^ 149 * Wasm.IEEE32.scaledValue b| := by
      positivity
    apply (div_le_iff₀ hdenPos).2
    have hzReal :
        |(z : ℝ)| ≤
          (Wasm.IEEE32.scaledMagnitude b : ℝ) * 2 ^ 126 := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤
          (Wasm.IEEE32.scaledMagnitude b : ℝ) * 2 ^ 126 := hzReal
      _ = divisionEpsilon *
          |(2 : ℝ) ^ 149 * Wasm.IEEE32.scaledValue b| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 149),
          hbAbs]
        norm_num [divisionEpsilon]
        ring

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

/-- Fuel-independent correctness of the hand-written WAT division program,
including the real error contract. -/
theorem div_program_terminates_real_error (a b : UInt32)
    (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE32.scaledMagnitude a ≤
      Wasm.IEEE32.scaledMagnitude b) :
    SmallStep.TerminatesWith (divConfig a b)
      (fun values _ =>
        values = [.f32 (Wasm.IEEE32.div a b)] ∧
          Finite (Wasm.IEEE32.div a b) ∧
          |value (Wasm.IEEE32.div a b) - value a / value b| ≤
            divisionEpsilon) := by
  have hresult := div_real_error a b ha hb hb0 hab
  exact (div_terminates a b).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

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
#print axioms div_real_error
#print axioms div_program_terminates_real_error
#print axioms div_program_terminates_finite_nonzero
#print axioms div_infinities
#print axioms div_positive_overflow

end CodeLib.IEEE32
