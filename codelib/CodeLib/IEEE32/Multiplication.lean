import CodeLib.IEEE32.SpecialValues
import CodeLib.IEEE32.Rounders
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

/-- The finite multiplication path is uniformly the dyadic rounder, including
signed-zero products. -/
theorem mul_finite_rounder (a b : UInt32) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE32.mul a b =
      Wasm.IEEE32.roundDyadicMagnitude
        (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
        (Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b) 149 := by
  have hna := not_nan_of_finite ha
  have hnb := not_nan_of_finite hb
  have hia := not_infinite_of_finite ha
  have hib := not_infinite_of_finite hb
  by_cases ha0 : Wasm.IEEE32.scaledMagnitude a = 0 <;>
    by_cases hb0 : Wasm.IEEE32.scaledMagnitude b = 0 <;>
    simp [Wasm.IEEE32.mul, hna, hnb, hia, hib, ha0, hb0,
      Wasm.IEEE32.roundDyadicMagnitude]

/-- On the bounded domain used by the examples, multiplication incurs at
most `2^275` after the exact equation is cleared by `2^149`.  Dividing by the
common `2^298` real denominator gives the usual absolute `2^-23` bound. -/
theorem mul_scaled_error (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (haBound : |Wasm.IEEE32.scaledValue a| ≤ (2 ^ 149 : Int))
    (hbBound : |Wasm.IEEE32.scaledValue b| ≤ (2 ^ 149 : Int)) :
    Finite (Wasm.IEEE32.mul a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.mul a b) * (2 : Int) ^ 149 -
        Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b| ≤
          (2 ^ 275 : Nat) := by
  have haMag : Wasm.IEEE32.scaledMagnitude a ≤ 2 ^ 149 := by
    rw [Int.abs_eq_natAbs, natAbs_scaledValue] at haBound
    exact_mod_cast haBound
  have hbMag : Wasm.IEEE32.scaledMagnitude b ≤ 2 ^ 149 := by
    rw [Int.abs_eq_natAbs, natAbs_scaledValue] at hbBound
    exact_mod_cast hbBound
  let n := Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b
  have hn : n < 2 ^ 300 := by
    calc
      n ≤ 2 ^ 149 * 2 ^ 149 := Nat.mul_le_mul haMag hbMag
      _ = 2 ^ 298 := by rw [← pow_add]
      _ < 2 ^ 300 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hs := roundDyadicMagnitude149_spec
    (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b) n hn
  have hmul := mul_finite_rounder a b ha hb
  rw [hmul]
  constructor
  · exact hs.1
  · have herr := hs.2.2
    have hresultSign := hs.2.1
    have habs (x y : Int) : |-x + y| = |x + -y| := by
      rw [show -x + y = -(x + -y) by ring, abs_neg]
    cases hsa : Wasm.IEEE32.sign a <;>
      cases hsb : Wasm.IEEE32.sign b <;>
      simp [n, hsa, hsb] at hresultSign <;>
      simp [Wasm.IEEE32.scaledValue, hresultSign, hsa, hsb, n] at herr ⊢
    all_goals
      first
      | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
      | rw [habs]
        simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

noncomputable def multiplicationEpsilon : ℝ := 1 / (2 : ℝ) ^ 23

theorem mul_real_error (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1) :
    Finite (Wasm.IEEE32.mul a b) ∧
      |value (Wasm.IEEE32.mul a b) - value a * value b| ≤
        multiplicationEpsilon := by
  have hs := mul_scaled_error a b ha hb
    (scaled_abs_le_of_value_abs_le a haBound)
    (scaled_abs_le_of_value_abs_le b hbBound)
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.mul a b) * (2 : Int) ^ 149 -
        Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b
    have hz : |z| ≤ (2 ^ 275 : Nat) := hs.2
    have heq :
        value (Wasm.IEEE32.mul a b) - value a * value b =
          (z : ℝ) / (2 : ℝ) ^ 298 := by
      simp [value, z]
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 298)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 298)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ 275 := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ 275 := hzReal
      _ = multiplicationEpsilon * (2 : ℝ) ^ 298 := by
        norm_num [multiplicationEpsilon]

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
#print axioms mul_real_error
#print axioms mul_program_terminates_finite_nonzero
#print axioms mul_infinities
#print axioms mul_largest_finite_by_two_overflows

end CodeLib.IEEE32
