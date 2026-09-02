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

/-- One modeled binary32 Horner stage, with both primitive rounding errors
made explicit in the conclusion. -/
theorem horner32_step_real_error (accumulator x coefficient : UInt32)
    (haccumulator : CodeLib.IEEE32.Finite accumulator)
    (hx : CodeLib.IEEE32.Finite x)
    (hcoefficient : CodeLib.IEEE32.Finite coefficient)
    (haccumulatorBound : |CodeLib.IEEE32.value accumulator| ≤ 1)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hcoefficientBound : |CodeLib.IEEE32.value coefficient| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE32.value (Wasm.IEEE32.mul accumulator x)| ≤ 1) :
    CodeLib.IEEE32.Finite
        (Wasm.IEEE32.add (Wasm.IEEE32.mul accumulator x) coefficient) ∧
      |CodeLib.IEEE32.value
          (Wasm.IEEE32.add (Wasm.IEEE32.mul accumulator x) coefficient) -
          (CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value coefficient)| ≤ 2 * f32Epsilon := by
  let product := Wasm.IEEE32.mul accumulator x
  have hproduct := CodeLib.IEEE32.mul_real_error accumulator x
    haccumulator hx haccumulatorBound hxBound
  change CodeLib.IEEE32.Finite product ∧
    |CodeLib.IEEE32.value product -
      CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x| ≤
        CodeLib.IEEE32.multiplicationEpsilon at hproduct
  have hsum := CodeLib.IEEE32.add_real_error product coefficient
    hproduct.1 hcoefficient hproductBound hcoefficientBound
  change CodeLib.IEEE32.Finite (Wasm.IEEE32.add product coefficient) ∧
    |CodeLib.IEEE32.value (Wasm.IEEE32.add product coefficient) -
      (CodeLib.IEEE32.value product +
        CodeLib.IEEE32.value coefficient)| ≤
        CodeLib.IEEE32.arithmeticEpsilon at hsum
  have hproductError :
      |CodeLib.IEEE32.value product -
        CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x| ≤
          f32Epsilon := by
    simpa [f32Epsilon, CodeLib.IEEE32.multiplicationEpsilon] using hproduct.2
  have hsumError :
      |CodeLib.IEEE32.value (Wasm.IEEE32.add product coefficient) -
        (CodeLib.IEEE32.value product +
          CodeLib.IEEE32.value coefficient)| ≤ f32Epsilon := by
    simpa [f32Epsilon, CodeLib.IEEE32.arithmeticEpsilon] using hsum.2
  have hsecond :
      |(0 : ℝ) -
        ((CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value coefficient) -
          (CodeLib.IEEE32.value product +
            CodeLib.IEEE32.value coefficient))| ≤ f32Epsilon := by
    rw [show (0 : ℝ) -
        ((CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value coefficient) -
          (CodeLib.IEEE32.value product +
            CodeLib.IEEE32.value coefficient)) =
        CodeLib.IEEE32.value product -
          CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x by ring]
    exact hproductError
  have hcomposed := CodeLib.Numerical.sum_perturbations
    (x := CodeLib.IEEE32.value (Wasm.IEEE32.add product coefficient))
    (x₀ := CodeLib.IEEE32.value product + CodeLib.IEEE32.value coefficient)
    (y := 0)
    (y₀ :=
      (CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
        CodeLib.IEEE32.value coefficient) -
      (CodeLib.IEEE32.value product + CodeLib.IEEE32.value coefficient))
    hsumError hsecond
  change CodeLib.IEEE32.Finite (Wasm.IEEE32.add product coefficient) ∧ _
  constructor
  · exact hsum.1
  · rw [show
      CodeLib.IEEE32.value (Wasm.IEEE32.add product coefficient) -
          (CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value coefficient) =
        (CodeLib.IEEE32.value (Wasm.IEEE32.add product coefficient) + 0) -
          ((CodeLib.IEEE32.value product +
              CodeLib.IEEE32.value coefficient) +
            ((CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
                CodeLib.IEEE32.value coefficient) -
              (CodeLib.IEEE32.value product +
                CodeLib.IEEE32.value coefficient))) by ring]
    convert hcomposed using 1 <;> ring

/-- Modeled left-to-right binary32 Horner fold. -/
def horner32 (x accumulator : UInt32) : List UInt32 → UInt32
  | [] => accumulator
  | coefficient :: coefficients =>
      horner32 x
        (Wasm.IEEE32.add (Wasm.IEEE32.mul accumulator x) coefficient)
        coefficients

/-- Coefficients paired with the two-error budget for each modeled stage. -/
noncomputable def horner32Stages (coefficients : List UInt32) :
    List (ℝ × ℝ) :=
  coefficients.map
    (fun word => (CodeLib.IEEE32.value word, 2 * f32Epsilon))

theorem horner32Stages_error_sum (coefficients : List UInt32) :
    ((horner32Stages coefficients).map Prod.snd).sum =
      (coefficients.length : ℝ) * (2 * f32Epsilon) := by
  induction coefficients with
  | nil => simp [horner32Stages]
  | cons coefficient coefficients ih =>
      change 2 * f32Epsilon +
          ((horner32Stages coefficients).map Prod.snd).sum =
        ((coefficients.length + 1 : Nat) : ℝ) * (2 * f32Epsilon)
      rw [ih]
      push_cast
      ring

/-- Exact real Horner target corresponding to `horner32`. -/
noncomputable def horner32Exact (x accumulator : UInt32)
    (coefficients : List UInt32) : ℝ :=
  CodeLib.Numerical.exactHorner (CodeLib.IEEE32.value x)
    (CodeLib.IEEE32.value accumulator) (horner32Stages coefficients)

/-- Every recursive Horner stage records exactly the hypotheses needed by its
modeled multiplication and addition, including the next accumulator's safety. -/
inductive Horner32Safe (x : UInt32) : UInt32 → List UInt32 → Prop
  | nil {accumulator : UInt32}
      (haccumulator : CodeLib.IEEE32.Finite accumulator) :
      Horner32Safe x accumulator []
  | cons {accumulator coefficient : UInt32} {coefficients : List UInt32}
      (haccumulator : CodeLib.IEEE32.Finite accumulator)
      (hx : CodeLib.IEEE32.Finite x)
      (hcoefficient : CodeLib.IEEE32.Finite coefficient)
      (haccumulatorBound : |CodeLib.IEEE32.value accumulator| ≤ 1)
      (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
      (hcoefficientBound : |CodeLib.IEEE32.value coefficient| ≤ 1)
      (hproductBound :
        |CodeLib.IEEE32.value (Wasm.IEEE32.mul accumulator x)| ≤ 1)
      (tail : Horner32Safe x
        (Wasm.IEEE32.add (Wasm.IEEE32.mul accumulator x) coefficient)
        coefficients) :
      Horner32Safe x accumulator (coefficient :: coefficients)

/-- Exact-real sufficient conditions for a sequence of binary32 Horner
stages.  Product headroom absorbs one unit error and stage headroom absorbs
the multiplication-plus-addition budget. -/
noncomputable def Horner32HeadroomStages (x accumulator : UInt32) :
    List UInt32 → Prop
  | [] => True
  | coefficient :: coefficients =>
      CodeLib.IEEE32.Finite coefficient ∧
      |CodeLib.IEEE32.value coefficient| ≤ 1 ∧
      |CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x| +
          f32Epsilon ≤ 1 ∧
      |CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
          CodeLib.IEEE32.value coefficient| + 2 * f32Epsilon ≤ 1 ∧
      Horner32HeadroomStages x
        (Wasm.IEEE32.add (Wasm.IEEE32.mul accumulator x) coefficient)
        coefficients

theorem mul32_value_bound_of_headroom (a b : UInt32)
    (ha : CodeLib.IEEE32.Finite a)
    (hb : CodeLib.IEEE32.Finite b)
    (haBound : |CodeLib.IEEE32.value a| ≤ 1)
    (hbBound : |CodeLib.IEEE32.value b| ≤ 1)
    (hheadroom :
      |CodeLib.IEEE32.value a * CodeLib.IEEE32.value b| +
        f32Epsilon ≤ 1) :
    |CodeLib.IEEE32.value (Wasm.IEEE32.mul a b)| ≤ 1 := by
  have hmul := CodeLib.IEEE32.mul_real_error a b ha hb haBound hbBound
  have herror :
      |CodeLib.IEEE32.value (Wasm.IEEE32.mul a b) -
        CodeLib.IEEE32.value a * CodeLib.IEEE32.value b| ≤ f32Epsilon := by
    simpa [f32Epsilon, CodeLib.IEEE32.multiplicationEpsilon] using hmul.2
  exact CodeLib.Numerical.abs_le_of_error_headroom herror hheadroom

theorem horner32_step_value_bound_of_headroom
    (accumulator x coefficient : UInt32)
    (haccumulator : CodeLib.IEEE32.Finite accumulator)
    (hx : CodeLib.IEEE32.Finite x)
    (hcoefficient : CodeLib.IEEE32.Finite coefficient)
    (haccumulatorBound : |CodeLib.IEEE32.value accumulator| ≤ 1)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hcoefficientBound : |CodeLib.IEEE32.value coefficient| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE32.value (Wasm.IEEE32.mul accumulator x)| ≤ 1)
    (hheadroom :
      |CodeLib.IEEE32.value accumulator * CodeLib.IEEE32.value x +
        CodeLib.IEEE32.value coefficient| + 2 * f32Epsilon ≤ 1) :
    |CodeLib.IEEE32.value
      (Wasm.IEEE32.add (Wasm.IEEE32.mul accumulator x) coefficient)| ≤ 1 := by
  have hstep := horner32_step_real_error accumulator x coefficient
    haccumulator hx hcoefficient haccumulatorBound hxBound
    hcoefficientBound hproductBound
  exact CodeLib.Numerical.abs_le_of_error_headroom hstep.2 hheadroom

/-- Exact-real headroom conditions construct the explicit modeled Horner
safety trace. -/
theorem horner32_safe_of_headroom (x accumulator : UInt32)
    (coefficients : List UInt32)
    (hx : CodeLib.IEEE32.Finite x)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (haccumulator : CodeLib.IEEE32.Finite accumulator)
    (haccumulatorBound : |CodeLib.IEEE32.value accumulator| ≤ 1)
    (hstages : Horner32HeadroomStages x accumulator coefficients) :
    Horner32Safe x accumulator coefficients := by
  induction coefficients generalizing accumulator with
  | nil => exact .nil haccumulator
  | cons coefficient coefficients ih =>
      simp only [Horner32HeadroomStages] at hstages
      rcases hstages with
        ⟨hcoefficient, hcoefficientBound, hproductHeadroom,
          hnextHeadroom, htail⟩
      have hproductBound := mul32_value_bound_of_headroom accumulator x
        haccumulator hx haccumulatorBound hxBound hproductHeadroom
      have hstep := horner32_step_real_error accumulator x coefficient
        haccumulator hx hcoefficient haccumulatorBound hxBound
        hcoefficientBound hproductBound
      have hnextBound := horner32_step_value_bound_of_headroom
        accumulator x coefficient haccumulator hx hcoefficient
        haccumulatorBound hxBound hcoefficientBound hproductBound
        hnextHeadroom
      exact .cons haccumulator hx hcoefficient haccumulatorBound hxBound
        hcoefficientBound hproductBound
        (ih _ hstep.1 hnextBound htail)

/-- The terminal accumulator of a safe binary32 Horner fold is finite. -/
theorem horner32_safe_finite (x accumulator : UInt32)
    (coefficients : List UInt32)
    (hsafe : Horner32Safe x accumulator coefficients) :
    CodeLib.IEEE32.Finite (horner32 x accumulator coefficients) := by
  induction hsafe with
  | nil haccumulator => simpa [horner32] using haccumulator
  | @cons accumulator coefficient coefficients haccumulator hx hcoefficient
      haccumulatorBound hxBound hcoefficientBound hproductBound tail ih =>
      simpa [horner32] using ih

/-- A safe binary32 fold supplies the format-independent Horner error trace. -/
theorem horner32_safe_trace (x accumulator : UInt32)
    (coefficients : List UInt32)
    (hsafe : Horner32Safe x accumulator coefficients) :
    CodeLib.Numerical.HornerApprox (CodeLib.IEEE32.value x)
      (CodeLib.IEEE32.value accumulator) (horner32Stages coefficients)
      (CodeLib.IEEE32.value (horner32 x accumulator coefficients)) := by
  induction coefficients generalizing accumulator with
  | nil =>
      exact CodeLib.Numerical.HornerApprox.nil _
  | cons coefficient coefficients ih =>
      cases hsafe with
      | cons haccumulator hx hcoefficient haccumulatorBound hxBound
          hcoefficientBound hproductBound tail =>
          have hstep := horner32_step_real_error accumulator x coefficient
            haccumulator hx hcoefficient haccumulatorBound hxBound
            hcoefficientBound hproductBound
          simpa [horner32, horner32Stages] using
            (CodeLib.Numerical.HornerApprox.cons hstep.2
              (ih _ tail))

/-- A safe modeled binary32 Horner fold stays finite and accumulates at most
two binary32 unit error budgets per stage on `|x| ≤ 1`. -/
theorem horner32_real_error (x accumulator : UInt32)
    (coefficients : List UInt32)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hsafe : Horner32Safe x accumulator coefficients) :
    CodeLib.IEEE32.Finite (horner32 x accumulator coefficients) ∧
      |CodeLib.IEEE32.value (horner32 x accumulator coefficients) -
          horner32Exact x accumulator coefficients| ≤
        (coefficients.length : ℝ) * (2 * f32Epsilon) := by
  constructor
  · exact horner32_safe_finite x accumulator coefficients hsafe
  · have herror := CodeLib.Numerical.horner_error_unit_interval
      hxBound
      (by simp :
        |CodeLib.IEEE32.value accumulator -
          CodeLib.IEEE32.value accumulator| ≤ (0 : ℝ))
      (horner32_safe_trace x accumulator coefficients hsafe)
    rw [horner32Stages_error_sum] at herror
    simpa [horner32Exact] using herror

/-- Exact-real headroom is a sufficient interface for the generic binary32
Horner finite/error theorem. -/
theorem horner32_real_error_of_headroom (x accumulator : UInt32)
    (coefficients : List UInt32)
    (hx : CodeLib.IEEE32.Finite x)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (haccumulator : CodeLib.IEEE32.Finite accumulator)
    (haccumulatorBound : |CodeLib.IEEE32.value accumulator| ≤ 1)
    (hstages : Horner32HeadroomStages x accumulator coefficients) :
    CodeLib.IEEE32.Finite (horner32 x accumulator coefficients) ∧
      |CodeLib.IEEE32.value (horner32 x accumulator coefficients) -
          horner32Exact x accumulator coefficients| ≤
        (coefficients.length : ℝ) * (2 * f32Epsilon) :=
  horner32_real_error x accumulator coefficients hxBound
    (horner32_safe_of_headroom x accumulator coefficients hx hxBound
      haccumulator haccumulatorBound hstages)

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
  have hstep := horner32_step_real_error a x b ha hx hb
    haBound hxBound hbBound hproductBound
  have hsafe : Horner32Safe x a [b] :=
    .cons ha hx hb haBound hxBound hbBound hproductBound (.nil hstep.1)
  simpa [horner32, horner32Exact, horner32Stages,
    CodeLib.Numerical.exactHorner, affineResult] using
      (horner32_real_error x a [b] hxBound hsafe)

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

/-- Fuel-independent correctness and the six-unit accumulated error bound for
the decoded three-stage f32 Horner WAT program.  `hsafe` contains the finite
and intermediate-magnitude hypotheses for all three modeled stages. -/
theorem horner3_program_real_error (x c₃ c₂ c₁ c₀ : UInt32)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hsafe : Horner32Safe x c₃ [c₂, c₁, c₀]) :
    SmallStep.TerminatesWith (horner3Config x c₃ c₂ c₁ c₀)
      (fun values _ =>
        values = [.f32 (horner3Result x c₃ c₂ c₁ c₀)] ∧
          CodeLib.IEEE32.Finite (horner3Result x c₃ c₂ c₁ c₀) ∧
          |CodeLib.IEEE32.value (horner3Result x c₃ c₂ c₁ c₀) -
              (((CodeLib.IEEE32.value c₃ * CodeLib.IEEE32.value x +
                  CodeLib.IEEE32.value c₂) * CodeLib.IEEE32.value x +
                CodeLib.IEEE32.value c₁) * CodeLib.IEEE32.value x +
                CodeLib.IEEE32.value c₀)| ≤ 6 * f32Epsilon) := by
  have hgeneric := horner32_real_error x c₃ [c₂, c₁, c₀] hxBound hsafe
  have hfinite :
      CodeLib.IEEE32.Finite (horner3Result x c₃ c₂ c₁ c₀) := by
    simpa [horner32, horner3Result] using hgeneric.1
  have herror :
      |CodeLib.IEEE32.value (horner3Result x c₃ c₂ c₁ c₀) -
          (((CodeLib.IEEE32.value c₃ * CodeLib.IEEE32.value x +
              CodeLib.IEEE32.value c₂) * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value c₁) * CodeLib.IEEE32.value x +
            CodeLib.IEEE32.value c₀)| ≤ 6 * f32Epsilon := by
    have h := hgeneric.2
    simp only [horner32, horner32Exact, horner32Stages,
      CodeLib.Numerical.exactHorner, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil] at h
    norm_num at h
    rw [show 6 * f32Epsilon = 3 * (2 * f32Epsilon) by ring]
    simpa [horner3Result] using h
  exact (horner3_terminates x c₃ c₂ c₁ c₀).mono
    (fun _values _store hvalues => ⟨hvalues, hfinite, herror⟩)

/-- The three-stage WAT result with exact-real headroom conditions replacing
direct obligations about rounded intermediate products. -/
theorem horner3_program_real_error_of_headroom (x c₃ c₂ c₁ c₀ : UInt32)
    (hx : CodeLib.IEEE32.Finite x)
    (hxBound : |CodeLib.IEEE32.value x| ≤ 1)
    (hc₃ : CodeLib.IEEE32.Finite c₃)
    (hc₃Bound : |CodeLib.IEEE32.value c₃| ≤ 1)
    (hstages : Horner32HeadroomStages x c₃ [c₂, c₁, c₀]) :
    SmallStep.TerminatesWith (horner3Config x c₃ c₂ c₁ c₀)
      (fun values _ =>
        values = [.f32 (horner3Result x c₃ c₂ c₁ c₀)] ∧
          CodeLib.IEEE32.Finite (horner3Result x c₃ c₂ c₁ c₀) ∧
          |CodeLib.IEEE32.value (horner3Result x c₃ c₂ c₁ c₀) -
              (((CodeLib.IEEE32.value c₃ * CodeLib.IEEE32.value x +
                  CodeLib.IEEE32.value c₂) * CodeLib.IEEE32.value x +
                CodeLib.IEEE32.value c₁) * CodeLib.IEEE32.value x +
                CodeLib.IEEE32.value c₀)| ≤ 6 * f32Epsilon) :=
  horner3_program_real_error x c₃ c₂ c₁ c₀ hxBound
    (horner32_safe_of_headroom x c₃ [c₂, c₁, c₀]
      hx hxBound hc₃ hc₃Bound hstages)

noncomputable def f64Epsilon : ℝ := 1 / (2 : ℝ) ^ 52

/-- One binary64 dot-product accumulation stage contributes one multiplication
error and one addition error. -/
theorem dot64_step_real_error (accumulator a b : UInt64)
    (haccumulator : CodeLib.IEEE64.Finite accumulator)
    (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b)
    (haccumulatorBound : |CodeLib.IEEE64.value accumulator| ≤ 1)
    (haBound : |CodeLib.IEEE64.value a| ≤ 1)
    (hbBound : |CodeLib.IEEE64.value b| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a b)| ≤ 1) :
    CodeLib.IEEE64.Finite
        (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)) ∧
      |CodeLib.IEEE64.value
          (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)) -
          (CodeLib.IEEE64.value accumulator +
            CodeLib.IEEE64.value a * CodeLib.IEEE64.value b)| ≤
        2 * f64Epsilon := by
  let product := Wasm.IEEE64.mul a b
  have hproduct := CodeLib.IEEE64.mul_real_error a b ha hb haBound hbBound
  change CodeLib.IEEE64.Finite product ∧
    |CodeLib.IEEE64.value product -
      CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤
        CodeLib.IEEE64.multiplicationEpsilon at hproduct
  have hsum := CodeLib.IEEE64.add_real_error accumulator product
    haccumulator hproduct.1 haccumulatorBound hproductBound
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add accumulator product) ∧
    |CodeLib.IEEE64.value (Wasm.IEEE64.add accumulator product) -
      (CodeLib.IEEE64.value accumulator +
        CodeLib.IEEE64.value product)| ≤
        CodeLib.IEEE64.arithmeticEpsilon at hsum
  have hproductError :
      |CodeLib.IEEE64.value product -
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤ f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.multiplicationEpsilon] using hproduct.2
  have hsumError :
      |CodeLib.IEEE64.value (Wasm.IEEE64.add accumulator product) -
        (CodeLib.IEEE64.value accumulator +
          CodeLib.IEEE64.value product)| ≤ f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.arithmeticEpsilon] using hsum.2
  have hsecond :
      |(0 : ℝ) -
        ((CodeLib.IEEE64.value accumulator +
            CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) -
          (CodeLib.IEEE64.value accumulator +
            CodeLib.IEEE64.value product))| ≤ f64Epsilon := by
    rw [show (0 : ℝ) -
        ((CodeLib.IEEE64.value accumulator +
            CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) -
          (CodeLib.IEEE64.value accumulator +
            CodeLib.IEEE64.value product)) =
        CodeLib.IEEE64.value product -
          CodeLib.IEEE64.value a * CodeLib.IEEE64.value b by ring]
    exact hproductError
  have hcomposed := CodeLib.Numerical.sum_perturbations
    (x := CodeLib.IEEE64.value (Wasm.IEEE64.add accumulator product))
    (x₀ := CodeLib.IEEE64.value accumulator + CodeLib.IEEE64.value product)
    (y := 0)
    (y₀ :=
      (CodeLib.IEEE64.value accumulator +
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) -
      (CodeLib.IEEE64.value accumulator + CodeLib.IEEE64.value product))
    hsumError hsecond
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add accumulator product) ∧ _
  constructor
  · exact hsum.1
  · rw [show
      CodeLib.IEEE64.value (Wasm.IEEE64.add accumulator product) -
          (CodeLib.IEEE64.value accumulator +
            CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) =
        (CodeLib.IEEE64.value (Wasm.IEEE64.add accumulator product) + 0) -
          ((CodeLib.IEEE64.value accumulator +
              CodeLib.IEEE64.value product) +
            ((CodeLib.IEEE64.value accumulator +
                CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) -
              (CodeLib.IEEE64.value accumulator +
                CodeLib.IEEE64.value product))) by ring]
    convert hcomposed using 1 <;> ring

/-- Modeled accumulation after the first term of a nonempty binary64 dot
product has established its initial accumulator. -/
def dot64Acc (accumulator : UInt64) : List (UInt64 × UInt64) → UInt64
  | [] => accumulator
  | (a, b) :: terms =>
      dot64Acc (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)) terms

/-- Exact real accumulation corresponding to `dot64Acc`. -/
noncomputable def dot64ExactAcc (accumulator : ℝ) :
    List (UInt64 × UInt64) → ℝ
  | [] => accumulator
  | (a, b) :: terms =>
      dot64ExactAcc
        (accumulator + CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) terms

/-- A nonempty modeled binary64 dot product. -/
def dot64 (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64)) : UInt64 :=
  dot64Acc (Wasm.IEEE64.mul first.1 first.2) rest

/-- Exact real target for `dot64`. -/
noncomputable def dot64Exact (first : UInt64 × UInt64)
    (rest : List (UInt64 × UInt64)) : ℝ :=
  dot64ExactAcc
    (CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2) rest

/-- Every input word in a binary64 dot product is finite and has real
magnitude at most one.  This is the common input domain of the primitive
multiplication theorem used by the fold. -/
def Dot64UnitInputs (terms : List (UInt64 × UInt64)) : Prop :=
  ∀ term ∈ terms,
    CodeLib.IEEE64.Finite term.1 ∧
    CodeLib.IEEE64.Finite term.2 ∧
    |CodeLib.IEEE64.value term.1| ≤ 1 ∧
    |CodeLib.IEEE64.value term.2| ≤ 1

/-- A uniform input envelope for a binary64 dot product.  The separate
`leftBound` and `rightBound` parameters make the resulting aggregate budget
usable for nonsymmetric kernels. -/
def Dot64UniformInputs (leftBound rightBound : ℝ)
    (terms : List (UInt64 × UInt64)) : Prop :=
  ∀ term ∈ terms,
    CodeLib.IEEE64.Finite term.1 ∧
    CodeLib.IEEE64.Finite term.2 ∧
    |CodeLib.IEEE64.value term.1| ≤ leftBound ∧
    |CodeLib.IEEE64.value term.2| ≤ rightBound

/-- Sum of the exact absolute product magnitudes.  This single aggregate is
enough to bound every exact partial dot product without assuming a sign
pattern. -/
noncomputable def dot64AbsMass : List (UInt64 × UInt64) → ℝ
  | [] => 0
  | (a, b) :: terms =>
      |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
        dot64AbsMass terms

/-- Absolute mass consumed by the first `count` terms. -/
noncomputable def dot64PrefixMass
    (terms : List (UInt64 × UInt64)) (count : Nat) : ℝ :=
  dot64AbsMass (terms.take count)

theorem dot64AbsMass_nonneg (terms : List (UInt64 × UInt64)) :
    0 ≤ dot64AbsMass terms := by
  induction terms with
  | nil => simp [dot64AbsMass]
  | cons term terms ih =>
      rcases term with ⟨a, b⟩
      simp only [dot64AbsMass]
      positivity

theorem dot64AbsMass_take_add_drop (terms : List (UInt64 × UInt64))
    (count : Nat) :
    dot64AbsMass (terms.take count) + dot64AbsMass (terms.drop count) =
      dot64AbsMass terms := by
  induction terms generalizing count with
  | nil => simp [dot64AbsMass]
  | cons term terms ih =>
      cases count with
      | zero => simp [dot64AbsMass]
      | succ count =>
          rcases term with ⟨a, b⟩
          simp only [List.take_succ_cons, List.drop_succ_cons, dot64AbsMass]
          rw [← ih count]
          ring

theorem dot64PrefixMass_le (terms : List (UInt64 × UInt64)) (count : Nat) :
    dot64PrefixMass terms count ≤ dot64AbsMass terms := by
  rw [dot64PrefixMass, ← dot64AbsMass_take_add_drop terms count]
  exact le_add_of_nonneg_right (dot64AbsMass_nonneg (terms.drop count))

theorem dot64UnitInputs_of_uniform
    (leftBound rightBound : ℝ) (terms : List (UInt64 × UInt64))
    (hleft : leftBound ≤ 1) (hright : rightBound ≤ 1)
    (hinputs : Dot64UniformInputs leftBound rightBound terms) :
    Dot64UnitInputs terms := by
  intro term hterm
  obtain ⟨hfiniteLeft, hfiniteRight, hboundLeft, hboundRight⟩ :=
    hinputs term hterm
  exact ⟨hfiniteLeft, hfiniteRight,
    hboundLeft.trans hleft, hboundRight.trans hright⟩

theorem dot64AbsMass_le_uniform
    (leftBound rightBound : ℝ) (terms : List (UInt64 × UInt64))
    (hleftNonneg : 0 ≤ leftBound) (hrightNonneg : 0 ≤ rightBound)
    (hinputs : Dot64UniformInputs leftBound rightBound terms) :
    dot64AbsMass terms ≤
      (terms.length : ℝ) * (leftBound * rightBound) := by
  induction terms with
  | nil => simp [dot64AbsMass]
  | cons term terms ih =>
      rcases term with ⟨a, b⟩
      have hhead := hinputs (a, b) (by simp)
      have htail : Dot64UniformInputs leftBound rightBound terms := by
        intro term hterm
        exact hinputs term (by simp [hterm])
      have hproduct :
          |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤
            leftBound * rightBound := by
        rw [abs_mul]
        exact mul_le_mul hhead.2.2.1 hhead.2.2.2
          (abs_nonneg _) hleftNonneg
      have henvelopeNonneg : 0 ≤ leftBound * rightBound :=
        mul_nonneg hleftNonneg hrightNonneg
      have hrest := ih htail
      simp only [dot64AbsMass, List.length_cons]
      push_cast
      nlinarith

/-- Each recursive dot-product stage exposes its finite-input and magnitude
hypotheses, plus safety of the accumulator produced for the tail. -/
inductive Dot64Safe : UInt64 → List (UInt64 × UInt64) → Prop
  | nil {accumulator : UInt64}
      (haccumulator : CodeLib.IEEE64.Finite accumulator) :
      Dot64Safe accumulator []
  | cons {accumulator a b : UInt64} {terms : List (UInt64 × UInt64)}
      (haccumulator : CodeLib.IEEE64.Finite accumulator)
      (ha : CodeLib.IEEE64.Finite a)
      (hb : CodeLib.IEEE64.Finite b)
      (haccumulatorBound : |CodeLib.IEEE64.value accumulator| ≤ 1)
      (haBound : |CodeLib.IEEE64.value a| ≤ 1)
      (hbBound : |CodeLib.IEEE64.value b| ≤ 1)
      (hproductBound :
        |CodeLib.IEEE64.value (Wasm.IEEE64.mul a b)| ≤ 1)
      (tail : Dot64Safe
        (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)) terms) :
      Dot64Safe accumulator ((a, b) :: terms)

/-- Exact-real sufficient conditions for dot-product tail stages.  Each
product reserves one binary64 unit error and each multiply-add target reserves
the two-unit local budget. -/
noncomputable def Dot64HeadroomStages (accumulator : UInt64) :
    List (UInt64 × UInt64) → Prop
  | [] => True
  | (a, b) :: terms =>
      CodeLib.IEEE64.Finite a ∧
      CodeLib.IEEE64.Finite b ∧
      |CodeLib.IEEE64.value a| ≤ 1 ∧
      |CodeLib.IEEE64.value b| ≤ 1 ∧
      |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
          f64Epsilon ≤ 1 ∧
      |CodeLib.IEEE64.value accumulator +
          CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
          2 * f64Epsilon ≤ 1 ∧
      Dot64HeadroomStages
        (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)) terms

theorem mul64_value_bound_of_headroom (a b : UInt64)
    (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b)
    (haBound : |CodeLib.IEEE64.value a| ≤ 1)
    (hbBound : |CodeLib.IEEE64.value b| ≤ 1)
    (hheadroom :
      |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
        f64Epsilon ≤ 1) :
    |CodeLib.IEEE64.value (Wasm.IEEE64.mul a b)| ≤ 1 := by
  have hmul := CodeLib.IEEE64.mul_real_error a b ha hb haBound hbBound
  have herror :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a b) -
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤ f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.multiplicationEpsilon] using hmul.2
  exact CodeLib.Numerical.abs_le_of_error_headroom herror hheadroom

theorem dot64_step_value_bound_of_headroom (accumulator a b : UInt64)
    (haccumulator : CodeLib.IEEE64.Finite accumulator)
    (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b)
    (haccumulatorBound : |CodeLib.IEEE64.value accumulator| ≤ 1)
    (haBound : |CodeLib.IEEE64.value a| ≤ 1)
    (hbBound : |CodeLib.IEEE64.value b| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul a b)| ≤ 1)
    (hheadroom :
      |CodeLib.IEEE64.value accumulator +
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
          2 * f64Epsilon ≤ 1) :
    |CodeLib.IEEE64.value
      (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b))| ≤ 1 := by
  have hstep := dot64_step_real_error accumulator a b haccumulator ha hb
    haccumulatorBound haBound hbBound hproductBound
  exact CodeLib.Numerical.abs_le_of_error_headroom hstep.2 hheadroom

/-- An aggregate exact absolute-mass budget constructs the recursive safety
trace needed by the modeled dot-product fold.  `exactAccumulator` and `error`
describe the prefix already accumulated; the remaining absolute product mass
and two primitive error units per remaining term reserve enough headroom for
every later multiplication and addition. -/
theorem dot64_safe_of_abs_mass_budget
    (accumulator : UInt64) (terms : List (UInt64 × UInt64))
    (exactAccumulator error : ℝ)
    (haccumulator : CodeLib.IEEE64.Finite accumulator)
    (haccumulatorError :
      |CodeLib.IEEE64.value accumulator - exactAccumulator| ≤ error)
    (hinputs : Dot64UnitInputs terms)
    (hbudget :
      |exactAccumulator| + error + dot64AbsMass terms +
          (terms.length : ℝ) * (2 * f64Epsilon) ≤ 1) :
    Dot64Safe accumulator terms := by
  induction terms generalizing accumulator exactAccumulator error with
  | nil => exact .nil haccumulator
  | cons term terms ih =>
      rcases term with ⟨a, b⟩
      let productExact :=
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b
      let next := Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)
      have hinput := hinputs (a, b) (by simp)
      obtain ⟨ha, hb, haBound, hbBound⟩ := hinput
      have htailInputs : Dot64UnitInputs terms := by
        intro term hterm
        exact hinputs term (by simp [hterm])
      have herrorNonneg : 0 ≤ error :=
        (abs_nonneg _).trans haccumulatorError
      have hepsilonNonneg : 0 ≤ f64Epsilon := by
        norm_num [f64Epsilon]
      have hmassNonneg : 0 ≤ dot64AbsMass terms :=
        dot64AbsMass_nonneg terms
      have htailErrorNonneg :
          0 ≤ (terms.length : ℝ) * (2 * f64Epsilon) := by
        positivity
      have hbudget' :
          |exactAccumulator| + error + |productExact| +
              dot64AbsMass terms + 2 * f64Epsilon +
              (terms.length : ℝ) * (2 * f64Epsilon) ≤ 1 := by
        change
          |exactAccumulator| + error +
                |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
              dot64AbsMass terms + 2 * f64Epsilon +
              (terms.length : ℝ) * (2 * f64Epsilon) ≤ 1
        have h := hbudget
        simp only [dot64AbsMass, List.length_cons, Nat.cast_add,
          Nat.cast_one] at h
        nlinarith
      have haccumulatorHeadroom :
          |exactAccumulator| + error ≤ 1 := by
        nlinarith [abs_nonneg exactAccumulator, abs_nonneg productExact]
      have haccumulatorBound :
          |CodeLib.IEEE64.value accumulator| ≤ 1 :=
        CodeLib.Numerical.abs_le_of_error_headroom
          haccumulatorError haccumulatorHeadroom
      have hproductHeadroom : |productExact| + f64Epsilon ≤ 1 := by
        nlinarith [abs_nonneg exactAccumulator]
      have hproductBound :
          |CodeLib.IEEE64.value (Wasm.IEEE64.mul a b)| ≤ 1 := by
        exact mul64_value_bound_of_headroom a b ha hb haBound hbBound
          (by simpa [productExact] using hproductHeadroom)
      have hstep := dot64_step_real_error accumulator a b
        haccumulator ha hb haccumulatorBound haBound hbBound hproductBound
      have hlocal :
          |(CodeLib.IEEE64.value next -
                (exactAccumulator + productExact)) -
              (CodeLib.IEEE64.value accumulator - exactAccumulator)| ≤
            2 * f64Epsilon := by
        rw [show
          (CodeLib.IEEE64.value next -
                (exactAccumulator + productExact)) -
              (CodeLib.IEEE64.value accumulator - exactAccumulator) =
            CodeLib.IEEE64.value next -
              (CodeLib.IEEE64.value accumulator + productExact) by ring]
        simpa [next, productExact] using hstep.2
      have hnextError :
          |CodeLib.IEEE64.value next -
              (exactAccumulator + productExact)| ≤
            error + 2 * f64Epsilon :=
        CodeLib.Numerical.sequential_perturbation
          haccumulatorError hlocal
      have hexactNextBound :
          |exactAccumulator + productExact| ≤
            |exactAccumulator| + |productExact| :=
        abs_add_le _ _
      have htailBudget :
          |exactAccumulator + productExact| +
                (error + 2 * f64Epsilon) + dot64AbsMass terms +
              (terms.length : ℝ) * (2 * f64Epsilon) ≤ 1 := by
        nlinarith
      have htail := ih next (exactAccumulator + productExact)
        (error + 2 * f64Epsilon) hstep.1 hnextError htailInputs htailBudget
      exact .cons haccumulator ha hb haccumulatorBound haBound hbBound
        hproductBound htail

/-- A nonempty dot product whose total exact absolute mass plus its complete
`2n - 1` primitive-error budget fits in the unit interval has a safe modeled
execution.  The public condition mentions only exact input values. -/
theorem dot64_safe_nonempty_of_abs_mass
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (hinputs : Dot64UnitInputs (first :: rest))
    (hbudget :
      dot64AbsMass (first :: rest) +
          (2 * (rest.length : ℝ) + 1) * f64Epsilon ≤ 1) :
    Dot64Safe (Wasm.IEEE64.mul first.1 first.2) rest := by
  have hfirst := hinputs first (by simp)
  obtain ⟨hfirstLeft, hfirstRight, hfirstLeftBound,
    hfirstRightBound⟩ := hfirst
  have hrestInputs : Dot64UnitInputs rest := by
    intro term hterm
    exact hinputs term (by simp [hterm])
  have hmul := CodeLib.IEEE64.mul_real_error first.1 first.2
    hfirstLeft hfirstRight hfirstLeftBound hfirstRightBound
  have hmulError :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul first.1 first.2) -
          CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2| ≤
        f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.multiplicationEpsilon] using hmul.2
  apply dot64_safe_of_abs_mass_budget
    (Wasm.IEEE64.mul first.1 first.2) rest
    (CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2)
    f64Epsilon hmul.1 hmulError hrestInputs
  have h := hbudget
  simp only [dot64AbsMass] at h
  nlinarith

/-- A convenient sufficient condition using uniform left/right operand
envelopes.  It replaces the exact absolute mass with `n * A * B`. -/
theorem dot64_safe_nonempty_of_uniform
    (leftBound rightBound : ℝ)
    (first : UInt64 × UInt64) (rest : List (UInt64 × UInt64))
    (hleftNonneg : 0 ≤ leftBound) (hrightNonneg : 0 ≤ rightBound)
    (hleftUnit : leftBound ≤ 1) (hrightUnit : rightBound ≤ 1)
    (hinputs : Dot64UniformInputs leftBound rightBound (first :: rest))
    (hbudget :
      ((rest.length : ℝ) + 1) * (leftBound * rightBound) +
          (2 * (rest.length : ℝ) + 1) * f64Epsilon ≤ 1) :
    Dot64Safe (Wasm.IEEE64.mul first.1 first.2) rest := by
  apply dot64_safe_nonempty_of_abs_mass first rest
    (dot64UnitInputs_of_uniform leftBound rightBound (first :: rest)
      hleftUnit hrightUnit hinputs)
  have hmass := dot64AbsMass_le_uniform leftBound rightBound
    (first :: rest) hleftNonneg hrightNonneg hinputs
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hmass
  nlinarith

/-- Exact-real headroom constructs the explicit modeled dot-product safety
trace. -/
theorem dot64_safe_of_headroom (accumulator : UInt64)
    (terms : List (UInt64 × UInt64))
    (haccumulator : CodeLib.IEEE64.Finite accumulator)
    (haccumulatorBound : |CodeLib.IEEE64.value accumulator| ≤ 1)
    (hstages : Dot64HeadroomStages accumulator terms) :
    Dot64Safe accumulator terms := by
  induction terms generalizing accumulator with
  | nil => exact .nil haccumulator
  | cons term terms ih =>
      rcases term with ⟨a, b⟩
      simp only [Dot64HeadroomStages] at hstages
      rcases hstages with
        ⟨ha, hb, haBound, hbBound, hproductHeadroom,
          hnextHeadroom, htail⟩
      have hproductBound := mul64_value_bound_of_headroom a b ha hb
        haBound hbBound hproductHeadroom
      have hstep := dot64_step_real_error accumulator a b haccumulator ha hb
        haccumulatorBound haBound hbBound hproductBound
      have hnextBound := dot64_step_value_bound_of_headroom accumulator a b
        haccumulator ha hb haccumulatorBound haBound hbBound hproductBound
        hnextHeadroom
      exact .cons haccumulator ha hb haccumulatorBound haBound hbBound
        hproductBound (ih _ hstep.1 hnextBound htail)

/-- An explicitly safe binary64 dot-product tail preserves an arbitrary
initial error budget and adds two unit budgets per additional term. -/
theorem dot64Acc_real_error (accumulator : UInt64)
    (terms : List (UInt64 × UInt64)) (exactAccumulator E : ℝ)
    (hsafe : Dot64Safe accumulator terms)
    (haccumulatorError :
      |CodeLib.IEEE64.value accumulator - exactAccumulator| ≤ E) :
    CodeLib.IEEE64.Finite (dot64Acc accumulator terms) ∧
      |CodeLib.IEEE64.value (dot64Acc accumulator terms) -
          dot64ExactAcc exactAccumulator terms| ≤
        E + (terms.length : ℝ) * (2 * f64Epsilon) := by
  induction terms generalizing accumulator exactAccumulator E with
  | nil =>
      cases hsafe with
      | nil haccumulator =>
          constructor
          · simpa [dot64Acc] using haccumulator
          · simpa [dot64Acc, dot64ExactAcc] using haccumulatorError
  | cons term terms ih =>
      rcases term with ⟨a, b⟩
      cases hsafe with
      | cons haccumulator ha hb haccumulatorBound haBound hbBound
          hproductBound tail =>
          let next := Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b)
          have hstep := dot64_step_real_error accumulator a b haccumulator ha hb
            haccumulatorBound haBound hbBound hproductBound
          have hlocal :
              |(CodeLib.IEEE64.value next -
                  (exactAccumulator +
                    CodeLib.IEEE64.value a * CodeLib.IEEE64.value b)) -
                (CodeLib.IEEE64.value accumulator - exactAccumulator)| ≤
                  2 * f64Epsilon := by
            rw [show
              (CodeLib.IEEE64.value next -
                  (exactAccumulator +
                    CodeLib.IEEE64.value a * CodeLib.IEEE64.value b)) -
                (CodeLib.IEEE64.value accumulator - exactAccumulator) =
              CodeLib.IEEE64.value next -
                (CodeLib.IEEE64.value accumulator +
                  CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) by ring]
            exact hstep.2
          have hnext := CodeLib.Numerical.sequential_perturbation
            haccumulatorError hlocal
          have htail := ih next
            (exactAccumulator +
              CodeLib.IEEE64.value a * CodeLib.IEEE64.value b)
            (E + 2 * f64Epsilon) tail hnext
          constructor
          · simpa [dot64Acc, next] using htail.1
          · change
              |CodeLib.IEEE64.value (dot64Acc next terms) -
                  dot64ExactAcc
                    (exactAccumulator +
                      CodeLib.IEEE64.value a * CodeLib.IEEE64.value b)
                    terms| ≤
                E + (((terms.length + 1 : Nat) : ℝ) * (2 * f64Epsilon))
            convert htail.2 using 1 <;> push_cast <;> ring

/-- A safe nonempty binary64 dot product has `2n - 1` primitive error
budgets: one for the first product and two for every remaining term. -/
theorem dot64_real_error (first : UInt64 × UInt64)
    (rest : List (UInt64 × UInt64))
    (hfirstLeft : CodeLib.IEEE64.Finite first.1)
    (hfirstRight : CodeLib.IEEE64.Finite first.2)
    (hfirstLeftBound : |CodeLib.IEEE64.value first.1| ≤ 1)
    (hfirstRightBound : |CodeLib.IEEE64.value first.2| ≤ 1)
    (hsafe : Dot64Safe (Wasm.IEEE64.mul first.1 first.2) rest) :
    CodeLib.IEEE64.Finite (dot64 first rest) ∧
      |CodeLib.IEEE64.value (dot64 first rest) - dot64Exact first rest| ≤
        (2 * (rest.length : ℝ) + 1) * f64Epsilon := by
  have hfirst := CodeLib.IEEE64.mul_real_error first.1 first.2
    hfirstLeft hfirstRight hfirstLeftBound hfirstRightBound
  have hfirstError :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul first.1 first.2) -
        CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2| ≤
          f64Epsilon := by
    simpa [f64Epsilon, CodeLib.IEEE64.multiplicationEpsilon] using hfirst.2
  have hresult := dot64Acc_real_error
    (Wasm.IEEE64.mul first.1 first.2) rest
    (CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2)
    f64Epsilon hsafe hfirstError
  constructor
  · simpa [dot64] using hresult.1
  · change
      |CodeLib.IEEE64.value
          (dot64Acc (Wasm.IEEE64.mul first.1 first.2) rest) -
        dot64ExactAcc
          (CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2) rest| ≤
        (2 * (rest.length : ℝ) + 1) * f64Epsilon
    convert hresult.2 using 1 <;> ring

/-- Exact-real headroom is a sufficient interface for the generic nonempty
binary64 dot-product theorem. -/
theorem dot64_real_error_of_headroom (first : UInt64 × UInt64)
    (rest : List (UInt64 × UInt64))
    (hfirstLeft : CodeLib.IEEE64.Finite first.1)
    (hfirstRight : CodeLib.IEEE64.Finite first.2)
    (hfirstLeftBound : |CodeLib.IEEE64.value first.1| ≤ 1)
    (hfirstRightBound : |CodeLib.IEEE64.value first.2| ≤ 1)
    (hfirstHeadroom :
      |CodeLib.IEEE64.value first.1 * CodeLib.IEEE64.value first.2| +
        f64Epsilon ≤ 1)
    (hstages : Dot64HeadroomStages
      (Wasm.IEEE64.mul first.1 first.2) rest) :
    CodeLib.IEEE64.Finite (dot64 first rest) ∧
      |CodeLib.IEEE64.value (dot64 first rest) - dot64Exact first rest| ≤
        (2 * (rest.length : ℝ) + 1) * f64Epsilon := by
  have hfirst := CodeLib.IEEE64.mul_real_error first.1 first.2
    hfirstLeft hfirstRight hfirstLeftBound hfirstRightBound
  have hfirstBound := mul64_value_bound_of_headroom first.1 first.2
    hfirstLeft hfirstRight hfirstLeftBound hfirstRightBound hfirstHeadroom
  exact dot64_real_error first rest hfirstLeft hfirstRight
    hfirstLeftBound hfirstRightBound
    (dot64_safe_of_headroom (Wasm.IEEE64.mul first.1 first.2) rest
      hfirst.1 hfirstBound hstages)

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
  have hadd := CodeLib.IEEE64.add_real_error product₀ product₁
    hp₀.1 hp₁.1 hproduct₀Bound hproduct₁Bound
  have hsafe : Dot64Safe product₀ [(a₁, b₁)] :=
    .cons hp₀.1 ha₁ hb₁ hproduct₀Bound ha₁Bound hb₁Bound
      hproduct₁Bound (.nil hadd.1)
  have hgeneric := dot64_real_error (a₀, b₀) [(a₁, b₁)]
    ha₀ hb₀ ha₀Bound hb₀Bound hsafe
  constructor
  · simpa [dot64, dot64Acc, dotResult] using hgeneric.1
  · change
      |CodeLib.IEEE64.value (Wasm.IEEE64.add product₀ product₁) -
          (CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
            CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁)| ≤
        3 * f64Epsilon
    have herror := hgeneric.2
    simp only [dot64, dot64Acc, dot64Exact, dot64ExactAcc,
      List.length_cons, List.length_nil, Nat.cast_one] at herror
    norm_num at herror
    exact herror

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

/-- Fuel-independent correctness and the seven-unit accumulated error bound
for the decoded four-term f64 dot-product WAT program.  `hsafe` records every
remaining finite-input, product, and accumulator magnitude obligation. -/
theorem dot4_program_real_error (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64)
    (ha₀ : CodeLib.IEEE64.Finite a₀)
    (hb₀ : CodeLib.IEEE64.Finite b₀)
    (ha₀Bound : |CodeLib.IEEE64.value a₀| ≤ 1)
    (hb₀Bound : |CodeLib.IEEE64.value b₀| ≤ 1)
    (hsafe : Dot64Safe (Wasm.IEEE64.mul a₀ b₀)
      [(a₁, b₁), (a₂, b₂), (a₃, b₃)]) :
    SmallStep.TerminatesWith
      (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)
      (fun values _ =>
        values = [.f64 (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)] ∧
          CodeLib.IEEE64.Finite
            (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) ∧
          |CodeLib.IEEE64.value
              (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) -
            (((CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
                CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁) +
              CodeLib.IEEE64.value a₂ * CodeLib.IEEE64.value b₂) +
              CodeLib.IEEE64.value a₃ * CodeLib.IEEE64.value b₃)| ≤
            7 * f64Epsilon) := by
  have hgeneric := dot64_real_error (a₀, b₀)
    [(a₁, b₁), (a₂, b₂), (a₃, b₃)]
    ha₀ hb₀ ha₀Bound hb₀Bound hsafe
  have hfinite : CodeLib.IEEE64.Finite
      (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) := by
    simpa [dot64, dot64Acc, dot4Result] using hgeneric.1
  have herror :
      |CodeLib.IEEE64.value
          (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) -
        (((CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
            CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁) +
          CodeLib.IEEE64.value a₂ * CodeLib.IEEE64.value b₂) +
          CodeLib.IEEE64.value a₃ * CodeLib.IEEE64.value b₃)| ≤
        7 * f64Epsilon := by
    have h := hgeneric.2
    simp only [dot64, dot64Acc, dot64Exact, dot64ExactAcc,
      List.length_cons, List.length_nil] at h
    norm_num at h
    simpa [dot4Result] using h
  exact (dot4_terminates a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃).mono
    (fun _values _store hvalues => ⟨hvalues, hfinite, herror⟩)

/-- The four-term WAT result with exact-real headroom replacing direct
rounded-intermediate magnitude obligations. -/
theorem dot4_program_real_error_of_headroom
    (a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : UInt64)
    (ha₀ : CodeLib.IEEE64.Finite a₀)
    (hb₀ : CodeLib.IEEE64.Finite b₀)
    (ha₀Bound : |CodeLib.IEEE64.value a₀| ≤ 1)
    (hb₀Bound : |CodeLib.IEEE64.value b₀| ≤ 1)
    (hfirstHeadroom :
      |CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀| +
        f64Epsilon ≤ 1)
    (hstages : Dot64HeadroomStages (Wasm.IEEE64.mul a₀ b₀)
      [(a₁, b₁), (a₂, b₂), (a₃, b₃)]) :
    SmallStep.TerminatesWith
      (dot4Config a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)
      (fun values _ =>
        values = [.f64 (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃)] ∧
          CodeLib.IEEE64.Finite
            (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) ∧
          |CodeLib.IEEE64.value
              (dot4Result a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃) -
            (((CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
                CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁) +
              CodeLib.IEEE64.value a₂ * CodeLib.IEEE64.value b₂) +
              CodeLib.IEEE64.value a₃ * CodeLib.IEEE64.value b₃)| ≤
            7 * f64Epsilon) :=
  dot4_program_real_error a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃
    ha₀ hb₀ ha₀Bound hb₀Bound
    (dot64_safe_of_headroom (Wasm.IEEE64.mul a₀ b₀)
      [(a₁, b₁), (a₂, b₂), (a₃, b₃)]
      (CodeLib.IEEE64.mul_real_error a₀ b₀ ha₀ hb₀
        ha₀Bound hb₀Bound).1
      (mul64_value_bound_of_headroom a₀ b₀ ha₀ hb₀
        ha₀Bound hb₀Bound hfirstHeadroom)
      hstages)

#print axioms horner32_step_real_error
#print axioms horner32_safe_finite
#print axioms horner32_safe_trace
#print axioms horner32_real_error
#print axioms horner32_safe_of_headroom
#print axioms horner32_real_error_of_headroom
#print axioms affine_real_error
#print axioms affine_program_real_error
#print axioms horner3_program_real_error
#print axioms horner3_program_real_error_of_headroom
#print axioms dot64_step_real_error
#print axioms dot64AbsMass_nonneg
#print axioms dot64AbsMass_take_add_drop
#print axioms dot64PrefixMass_le
#print axioms dot64UnitInputs_of_uniform
#print axioms dot64AbsMass_le_uniform
#print axioms dot64_safe_of_abs_mass_budget
#print axioms dot64_safe_nonempty_of_abs_mass
#print axioms dot64_safe_nonempty_of_uniform
#print axioms dot64Acc_real_error
#print axioms dot64_real_error
#print axioms dot64_safe_of_headroom
#print axioms dot64_real_error_of_headroom
#print axioms dot_real_error
#print axioms dot_program_real_error
#print axioms dot4_program_real_error
#print axioms dot4_program_real_error_of_headroom

end CodeLib.Numerical.Kernels
