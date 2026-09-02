import CodeLib.IEEE32.Multiplication
import CodeLib.IEEE64.Operations
import CodeLib.Numerical.ErrorComposition
import Interpreter.Wasm.Examples.FloatNumericalKernels

/-!
# Quantitative numerical-kernel specifications

The hypotheses expose every finite-input, operand-magnitude, and intermediate
magnitude condition used to exclude overflow.  Neither representative kernel
contains division, so no denominator restriction is needed.
-/

namespace CodeLib.Numerical.Kernels

open Wasm
open Wasm.FloatNumericalKernels

noncomputable def f32Epsilon : ℝ := 1 / (2 : ℝ) ^ 23

/-- The decoded f32 affine kernel has at most two primitive rounding errors.
`hproductBound` is the explicit intermediate-magnitude/overflow-exclusion
condition for the final addition. -/
theorem affine_real_error (a x b : UInt32)
    (ha : CodeLib.IEEE32.Finite a)
    (hx : CodeLib.IEEE32.Finite x)
    (hb : CodeLib.IEEE32.Finite b)
    (haBound : |CodeLib.IEEE32.value a| ≤ 1)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hbBound : |CodeLib.IEEE32.value b| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE32.value (Wasm.IEEE32.mul a x)| ≤ 1) :
    CodeLib.IEEE32.Finite (affineResult a x b) ∧
      |CodeLib.IEEE32.value (affineResult a x b) -
          (CodeLib.IEEE32.value a * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value b)| ≤ 2 * f32Epsilon := by
  let product := Wasm.IEEE32.mul a x
  have hproduct := CodeLib.IEEE32.mul_real_error
    a x ha hx haBound hxBound
  change CodeLib.IEEE32.Finite product ∧
    |CodeLib.IEEE32.value product -
      CodeLib.IEEE32.value a * CodeLib.IEEE32.value x| ≤
        CodeLib.IEEE32.multiplicationEpsilon at hproduct
  have hsum := CodeLib.IEEE32.add_real_error
    product b hproduct.1 hb hproductBound hbBound
  change CodeLib.IEEE32.Finite (Wasm.IEEE32.add product b) ∧
    |CodeLib.IEEE32.value (Wasm.IEEE32.add product b) -
      (CodeLib.IEEE32.value product + CodeLib.IEEE32.value b)| ≤
        CodeLib.IEEE32.arithmeticEpsilon at hsum
  have hproductError :
      |CodeLib.IEEE32.value product -
        CodeLib.IEEE32.value a * CodeLib.IEEE32.value x| ≤
          f32Epsilon := by
    simpa [f32Epsilon, CodeLib.IEEE32.multiplicationEpsilon] using hproduct.2
  have hsumError :
      |CodeLib.IEEE32.value (Wasm.IEEE32.add product b) -
        (CodeLib.IEEE32.value product + CodeLib.IEEE32.value b)| ≤
          f32Epsilon := by
    simpa [f32Epsilon, CodeLib.IEEE32.arithmeticEpsilon] using hsum.2
  have hsecond :
      |(0 : ℝ) -
        ((CodeLib.IEEE32.value a * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value b) -
          (CodeLib.IEEE32.value product + CodeLib.IEEE32.value b))| ≤
        f32Epsilon := by
    rw [show (0 : ℝ) -
        ((CodeLib.IEEE32.value a * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value b) -
          (CodeLib.IEEE32.value product + CodeLib.IEEE32.value b)) =
        CodeLib.IEEE32.value product -
          CodeLib.IEEE32.value a * CodeLib.IEEE32.value x by ring]
    exact hproductError
  have hcomposed := CodeLib.Numerical.sum_perturbations
    (x := CodeLib.IEEE32.value (Wasm.IEEE32.add product b))
    (x₀ := CodeLib.IEEE32.value product + CodeLib.IEEE32.value b)
    (y := 0)
    (y₀ :=
      (CodeLib.IEEE32.value a * CodeLib.IEEE32.value x +
        CodeLib.IEEE32.value b) -
      (CodeLib.IEEE32.value product + CodeLib.IEEE32.value b))
    hsumError hsecond
  change CodeLib.IEEE32.Finite (Wasm.IEEE32.add product b) ∧ _
  constructor
  · exact hsum.1
  · change
      |CodeLib.IEEE32.value (Wasm.IEEE32.add product b) -
          (CodeLib.IEEE32.value a * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value b)| ≤ 2 * f32Epsilon
    convert hcomposed using 1 <;> ring

/-- Fuel-independent end-to-end correctness and accumulated error for the
decoded f32 affine WAT program. -/
theorem affine_program_real_error (a x b : UInt32)
    (ha : CodeLib.IEEE32.Finite a)
    (hx : CodeLib.IEEE32.Finite x)
    (hb : CodeLib.IEEE32.Finite b)
    (haBound : |CodeLib.IEEE32.value a| ≤ 1)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hbBound : |CodeLib.IEEE32.value b| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE32.value (Wasm.IEEE32.mul a x)| ≤ 1) :
    SmallStep.TerminatesWith (affineConfig a x b)
      (fun values _ =>
        values = [.f32 (affineResult a x b)] ∧
          CodeLib.IEEE32.Finite (affineResult a x b) ∧
          |CodeLib.IEEE32.value (affineResult a x b) -
              (CodeLib.IEEE32.value a * CodeLib.IEEE32.value x +
                CodeLib.IEEE32.value b)| ≤ 2 * f32Epsilon) := by
  have hresult := affine_real_error a x b ha hx hb
    haBound hxBound hbBound hproductBound
  exact (affine_terminates a x b).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

noncomputable def f64Epsilon : ℝ := 1 / (2 : ℝ) ^ 52

/-- A two-term binary64 dot product has the two multiplication errors plus the
final addition error.  `hproduct₀Bound` and `hproduct₁Bound` explicitly
exclude overflow in the intermediate products and final addition. -/
theorem dot_real_error (a₀ b₀ a₁ b₁ : UInt64)
    (ha₀ : CodeLib.IEEE64.Finite a₀) (hb₀ : CodeLib.IEEE64.Finite b₀)
    (ha₁ : CodeLib.IEEE64.Finite a₁) (hb₁ : CodeLib.IEEE64.Finite b₁)
    (ha₀Bound : |CodeLib.IEEE64.value a₀| ≤ 1)
    (hb₀Bound : |CodeLib.IEEE64.value b₀| ≤ 1)
    (ha₁Bound : |CodeLib.IEEE64.value a₁| ≤ 1)
    (hb₁Bound : |CodeLib.IEEE64.value b₁| ≤ 1)
    (hproduct₀Bound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a₀ b₀)| ≤ 1)
    (hproduct₁Bound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a₁ b₁)| ≤ 1) :
    CodeLib.IEEE64.Finite (dotResult a₀ b₀ a₁ b₁) ∧
      |CodeLib.IEEE64.value (dotResult a₀ b₀ a₁ b₁) -
          (CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
            CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁)| ≤
        3 * f64Epsilon := by
  let product₀ := Wasm.IEEE64.mul a₀ b₀
  let product₁ := Wasm.IEEE64.mul a₁ b₁
  have hp₀ := CodeLib.IEEE64.mul_real_error
    a₀ b₀ ha₀ hb₀ ha₀Bound hb₀Bound
  have hp₁ := CodeLib.IEEE64.mul_real_error
    a₁ b₁ ha₁ hb₁ ha₁Bound hb₁Bound
  change CodeLib.IEEE64.Finite product₀ ∧
    |CodeLib.IEEE64.value product₀ -
      CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀| ≤
        CodeLib.IEEE64.multiplicationEpsilon at hp₀
  change CodeLib.IEEE64.Finite product₁ ∧
    |CodeLib.IEEE64.value product₁ -
      CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁| ≤
        CodeLib.IEEE64.multiplicationEpsilon at hp₁
  have hadd := CodeLib.IEEE64.add_real_error product₀ product₁
    hp₀.1 hp₁.1 hproduct₀Bound hproduct₁Bound
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add product₀ product₁) ∧
    |CodeLib.IEEE64.value (Wasm.IEEE64.add product₀ product₁) -
      (CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁)| ≤
        CodeLib.IEEE64.arithmeticEpsilon at hadd
  have hp₀Error :
      |CodeLib.IEEE64.value product₀ -
        CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀| ≤
          f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.multiplicationEpsilon] using hp₀.2
  have hp₁Error :
      |CodeLib.IEEE64.value product₁ -
        CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁| ≤
          f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.multiplicationEpsilon] using hp₁.2
  have hproducts := CodeLib.Numerical.sum_perturbations hp₀Error hp₁Error
  have haddError :
      |CodeLib.IEEE64.value (Wasm.IEEE64.add product₀ product₁) -
        (CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁)| ≤
          f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.arithmeticEpsilon] using hadd.2
  let exactSum :=
    CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
      CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁
  have hsecond :
      |(0 : ℝ) -
        (exactSum -
          (CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁))| ≤
        f64Epsilon + f64Epsilon := by
    rw [show (0 : ℝ) -
        (exactSum -
          (CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁)) =
      (CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁) -
        exactSum by ring]
    simpa [exactSum] using hproducts
  have hcomposed := CodeLib.Numerical.sum_perturbations
    (x := CodeLib.IEEE64.value (Wasm.IEEE64.add product₀ product₁))
    (x₀ := CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁)
    (y := 0) (y₀ := exactSum -
      (CodeLib.IEEE64.value product₀ + CodeLib.IEEE64.value product₁))
    haddError hsecond
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add product₀ product₁) ∧ _
  constructor
  · exact hadd.1
  · change
      |CodeLib.IEEE64.value (Wasm.IEEE64.add product₀ product₁) -
          (CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
            CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁)| ≤
        3 * f64Epsilon
    dsimp only [exactSum] at hcomposed
    convert hcomposed using 1 <;> ring

/-- Fuel-independent end-to-end correctness and accumulated error for the
decoded two-term f64 dot-product WAT program. -/
theorem dot_program_real_error (a₀ b₀ a₁ b₁ : UInt64)
    (ha₀ : CodeLib.IEEE64.Finite a₀) (hb₀ : CodeLib.IEEE64.Finite b₀)
    (ha₁ : CodeLib.IEEE64.Finite a₁) (hb₁ : CodeLib.IEEE64.Finite b₁)
    (ha₀Bound : |CodeLib.IEEE64.value a₀| ≤ 1)
    (hb₀Bound : |CodeLib.IEEE64.value b₀| ≤ 1)
    (ha₁Bound : |CodeLib.IEEE64.value a₁| ≤ 1)
    (hb₁Bound : |CodeLib.IEEE64.value b₁| ≤ 1)
    (hproduct₀Bound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a₀ b₀)| ≤ 1)
    (hproduct₁Bound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a₁ b₁)| ≤ 1) :
    SmallStep.TerminatesWith (dotConfig a₀ b₀ a₁ b₁)
      (fun values _ =>
        values = [.f64 (dotResult a₀ b₀ a₁ b₁)] ∧
          CodeLib.IEEE64.Finite (dotResult a₀ b₀ a₁ b₁) ∧
          |CodeLib.IEEE64.value (dotResult a₀ b₀ a₁ b₁) -
              (CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
                CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁)| ≤
            3 * f64Epsilon) := by
  have hresult := dot_real_error a₀ b₀ a₁ b₁ ha₀ hb₀ ha₁ hb₁
    ha₀Bound hb₀Bound ha₁Bound hb₁Bound hproduct₀Bound hproduct₁Bound
  exact (dot_terminates a₀ b₀ a₁ b₁).mono
    (fun _values _store hvalues => ⟨hvalues, hresult.1, hresult.2⟩)

#print axioms affine_real_error
#print axioms affine_program_real_error
#print axioms dot_real_error
#print axioms dot_program_real_error

end CodeLib.Numerical.Kernels
