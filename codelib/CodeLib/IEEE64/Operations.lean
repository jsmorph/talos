import CodeLib.IEEE64.Rounders
import Interpreter.Wasm.Examples.Float64Multiplication
import Interpreter.Wasm.Examples.IEEE64
import Mathlib.Tactic

/-!
# Binary64 operation specifications
-/

namespace CodeLib.IEEE64

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

open Wasm
open Wasm.Float64Multiplication

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
#print axioms mul_program_exact
#print axioms mul_real_error
#print axioms mul_program_real_error
#print axioms arithmetic_examples

end CodeLib.IEEE64
