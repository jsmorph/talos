import Mathlib.Tactic

/-!
# Reusable real error-composition lemmas

These lemmas are independent of a particular floating-point format.  Every
primitive error and magnitude budget is an explicit argument.
-/

namespace CodeLib.Numerical

/-- Errors of two independently perturbed summands add. -/
theorem sum_perturbations {x x₀ y y₀ eₓ eᵧ : ℝ}
    (hx : |x - x₀| ≤ eₓ) (hy : |y - y₀| ≤ eᵧ) :
    |(x + y) - (x₀ + y₀)| ≤ eₓ + eᵧ := by
  rw [show (x + y) - (x₀ + y₀) = (x - x₀) + (y - y₀) by ring]
  exact (abs_add_le _ _).trans (add_le_add hx hy)

/-- Product error including the second-order perturbation term. -/
theorem product_perturbations {x x₀ y y₀ eₓ eᵧ Mₓ Mᵧ : ℝ}
    (hx : |x - x₀| ≤ eₓ) (hy : |y - y₀| ≤ eᵧ)
    (hx₀ : |x₀| ≤ Mₓ) (hy₀ : |y₀| ≤ Mᵧ) :
    |x * y - x₀ * y₀| ≤ eₓ * eᵧ + eₓ * Mᵧ + Mₓ * eᵧ := by
  rw [show x * y - x₀ * y₀ =
    (x - x₀) * (y - y₀) + (x - x₀) * y₀ + x₀ * (y - y₀) by ring]
  calc
    |(x - x₀) * (y - y₀) + (x - x₀) * y₀ + x₀ * (y - y₀)| ≤
        |(x - x₀) * (y - y₀)| + |(x - x₀) * y₀| +
          |x₀ * (y - y₀)| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |x - x₀| * |y - y₀| + |x - x₀| * |y₀| +
          |x₀| * |y - y₀| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ eₓ * eᵧ + eₓ * Mᵧ + Mₓ * eᵧ := by
      have heₓ : 0 ≤ eₓ := (abs_nonneg _).trans hx
      have heᵧ : 0 ≤ eᵧ := (abs_nonneg _).trans hy
      have hMₓ : 0 ≤ Mₓ := (abs_nonneg _).trans hx₀
      exact add_le_add
        (add_le_add
          (mul_le_mul hx hy (abs_nonneg _) heₓ)
          (mul_le_mul hx hy₀ (abs_nonneg _) heₓ))
        (mul_le_mul hx₀ hy (abs_nonneg _) hMₓ)

/-- Dividing an approximation and its target by the same exact nonzero
constant scales absolute error by `1 / |c|`. -/
theorem division_by_exact_constant {x x₀ c e : ℝ}
    (hc : c ≠ 0) (hx : |x - x₀| ≤ e) :
    |x / c - x₀ / c| ≤ e / |c| := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  rw [show x / c - x₀ / c = (x - x₀) / c by ring, abs_div]
  exact (div_le_div_iff_of_pos_right hcabs).2 hx

/-- Two sequential Horner steps accumulate the second primitive error plus
the first error amplified by the argument-magnitude budget. -/
theorem horner_two_step {x a b c r₁ r₂ e₁ e₂ M : ℝ}
    (hx : |x| ≤ M)
    (h₁ : |r₁ - (a * x + b)| ≤ e₁)
    (h₂ : |r₂ - (r₁ * x + c)| ≤ e₂) :
    |r₂ - ((a * x + b) * x + c)| ≤ e₂ + e₁ * M := by
  rw [show r₂ - ((a * x + b) * x + c) =
    (r₂ - (r₁ * x + c)) + (r₁ - (a * x + b)) * x by ring]
  calc
    |(r₂ - (r₁ * x + c)) + (r₁ - (a * x + b)) * x| ≤
        |r₂ - (r₁ * x + c)| + |(r₁ - (a * x + b)) * x| :=
      abs_add_le _ _
    _ = |r₂ - (r₁ * x + c)| + |r₁ - (a * x + b)| * |x| := by
      rw [abs_mul]
    _ ≤ e₂ + e₁ * M := by
      exact add_le_add h₂
        (mul_le_mul h₁ hx (abs_nonneg _) (le_trans (abs_nonneg _) h₁))

#print axioms sum_perturbations
#print axioms product_perturbations
#print axioms division_by_exact_constant
#print axioms horner_two_step

end CodeLib.Numerical
