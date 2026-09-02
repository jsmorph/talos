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

/-- A list of independently perturbed summands is bounded by the sum of its
individual error budgets.  Pairing each approximation with its target avoids
an auxiliary list-length side condition. -/
theorem list_sum_perturbations (terms : List (ℝ × ℝ)) (error : ℝ × ℝ → ℝ)
    (herror : ∀ term ∈ terms, |term.1 - term.2| ≤ error term) :
    |(terms.map Prod.fst).sum - (terms.map Prod.snd).sum| ≤
      (terms.map error).sum := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons]
      apply sum_perturbations
      · exact herror term (by simp)
      · apply ih
        intro other hother
        exact herror other (by simp [hother])

/-- One sequential update adds its local perturbation to the error already
accumulated by the preceding updates. -/
theorem sequential_perturbation {r s r' s' E δ : ℝ}
    (hprevious : |r - s| ≤ E)
    (hlocal : |(r' - s') - (r - s)| ≤ δ) :
    |r' - s'| ≤ E + δ := by
  rw [show r' - s' = (r - s) + ((r' - s') - (r - s)) by ring]
  exact (abs_add_le _ _).trans (add_le_add hprevious hlocal)

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

/-- An exact value with enough magnitude headroom to absorb a known absolute
error gives a direct magnitude bound for the approximation. -/
theorem abs_le_of_error_headroom {approximate exact error bound : ℝ}
    (herror : |approximate - exact| ≤ error)
    (hheadroom : |exact| + error ≤ bound) :
    |approximate| ≤ bound := by
  rw [show approximate = (approximate - exact) + exact by ring]
  calc
    |approximate - exact + exact| ≤
        |approximate - exact| + |exact| := abs_add_le _ _
    _ ≤ error + |exact| := add_le_add herror (le_refl _)
    _ = |exact| + error := add_comm _ _
    _ ≤ bound := hheadroom

/-! ## Sequential Horner evaluation -/

/-- Exact Horner evaluation.  Each pair contains the next coefficient and the
local error budget assigned to that stage; the budget is ignored here. -/
def exactHorner (x : ℝ) : ℝ → List (ℝ × ℝ) → ℝ
  | accumulator, [] => accumulator
  | accumulator, (coefficient, _) :: stages =>
      exactHorner x (accumulator * x + coefficient) stages

/-- Propagate an initial error through Horner stages.  A stage first amplifies
the accumulated error by `ρ`, then adds its own local error budget. -/
def hornerErrorBudget (ρ : ℝ) : ℝ → List (ℝ × ℝ) → ℝ
  | accumulated, [] => accumulated
  | accumulated, (_, localError) :: stages =>
      hornerErrorBudget ρ (localError + accumulated * ρ) stages

/-- The closed-form weighted sum of local Horner errors. -/
def weightedHornerErrors (ρ : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (_, localError) :: stages =>
      localError * ρ ^ stages.length + weightedHornerErrors ρ stages

/-- An explicit trace of approximate Horner accumulators. -/
inductive HornerApprox (x : ℝ) : ℝ → List (ℝ × ℝ) → ℝ → Prop
  | nil (accumulator : ℝ) : HornerApprox x accumulator [] accumulator
  | cons {accumulator rounded output coefficient localError : ℝ}
      {stages : List (ℝ × ℝ)}
      (hlocal :
        |rounded - (accumulator * x + coefficient)| ≤ localError)
      (tail : HornerApprox x rounded stages output) :
      HornerApprox x accumulator ((coefficient, localError) :: stages) output

/-- One Horner stage amplifies the preceding error by at most the argument
magnitude and adds the stage's primitive error. -/
theorem horner_error_step {x ρ r s r' c E δ : ℝ}
    (hx : |x| ≤ ρ) (hprevious : |r - s| ≤ E)
    (hlocal : |r' - (r * x + c)| ≤ δ) :
    |r' - (s * x + c)| ≤ δ + E * ρ := by
  rw [show r' - (s * x + c) =
    (r' - (r * x + c)) + (r - s) * x by ring]
  calc
    |(r' - (r * x + c)) + (r - s) * x| ≤
        |r' - (r * x + c)| + |(r - s) * x| := abs_add_le _ _
    _ = |r' - (r * x + c)| + |r - s| * |x| := by rw [abs_mul]
    _ ≤ δ + E * ρ := by
      exact add_le_add hlocal
        (mul_le_mul hprevious hx (abs_nonneg _)
          (le_trans (abs_nonneg _) hprevious))

/-- A complete approximate Horner trace satisfies the recursively accumulated
error budget. -/
theorem horner_error_recurrence {x ρ approximateSeed exactSeed output E : ℝ}
    {stages : List (ℝ × ℝ)}
    (hx : |x| ≤ ρ)
    (hseed : |approximateSeed - exactSeed| ≤ E)
    (htrace : HornerApprox x approximateSeed stages output) :
    |output - exactHorner x exactSeed stages| ≤
      hornerErrorBudget ρ E stages := by
  induction htrace generalizing exactSeed E with
  | nil accumulator => simpa [exactHorner, hornerErrorBudget] using hseed
  | @cons accumulator rounded output coefficient localError stages
      hlocal tail ih =>
      have hstep := horner_error_step hx hseed hlocal
      simpa [exactHorner, hornerErrorBudget] using
        (ih (exactSeed := exactSeed * x + coefficient)
          (E := localError + E * ρ) hstep)

/-- The recursive Horner budget equals the initial error amplified across all
stages plus the weighted sum of local errors. -/
theorem hornerErrorBudget_closed_form (ρ E : ℝ)
    (stages : List (ℝ × ℝ)) :
    hornerErrorBudget ρ E stages =
      E * ρ ^ stages.length + weightedHornerErrors ρ stages := by
  induction stages generalizing E with
  | nil => simp [hornerErrorBudget, weightedHornerErrors]
  | cons stage stages ih =>
      rcases stage with ⟨coefficient, localError⟩
      simp only [hornerErrorBudget]
      rw [ih]
      simp only [List.length_cons, weightedHornerErrors, pow_succ]
      ring

theorem weightedHornerErrors_one (stages : List (ℝ × ℝ)) :
    weightedHornerErrors 1 stages = (stages.map Prod.snd).sum := by
  induction stages with
  | nil => simp [weightedHornerErrors]
  | cons stage stages ih =>
      rcases stage with ⟨coefficient, localError⟩
      simp [weightedHornerErrors, ih]

theorem hornerErrorBudget_one (E : ℝ) (stages : List (ℝ × ℝ)) :
    hornerErrorBudget 1 E stages = E + (stages.map Prod.snd).sum := by
  rw [hornerErrorBudget_closed_form, weightedHornerErrors_one]
  simp

/-- When `|x| ≤ 1`, no earlier Horner error is amplified; total error is at
most the initial error plus the sum of all local budgets. -/
theorem horner_error_unit_interval
    {x approximateSeed exactSeed output E : ℝ}
    {stages : List (ℝ × ℝ)}
    (hx : |x| ≤ 1)
    (hseed : |approximateSeed - exactSeed| ≤ E)
    (htrace : HornerApprox x approximateSeed stages output) :
    |output - exactHorner x exactSeed stages| ≤
      E + (stages.map Prod.snd).sum := by
  have h := horner_error_recurrence hx hseed htrace
  rw [hornerErrorBudget_one] at h
  exact h

/-- Two sequential Horner steps accumulate the second primitive error plus
the first error amplified by the argument-magnitude budget. -/
theorem horner_two_step {x a b c r₁ r₂ e₁ e₂ M : ℝ}
    (hx : |x| ≤ M)
    (h₁ : |r₁ - (a * x + b)| ≤ e₁)
    (h₂ : |r₂ - (r₁ * x + c)| ≤ e₂) :
    |r₂ - ((a * x + b) * x + c)| ≤ e₂ + e₁ * M := by
  have htrace : HornerApprox x a [(b, e₁), (c, e₂)] r₂ :=
    .cons h₁ (.cons h₂ (.nil r₂))
  have h := horner_error_recurrence hx (by simp : |a - a| ≤ (0 : ℝ)) htrace
  simpa [exactHorner, hornerErrorBudget] using h

#print axioms sum_perturbations
#print axioms list_sum_perturbations
#print axioms sequential_perturbation
#print axioms product_perturbations
#print axioms division_by_exact_constant
#print axioms abs_le_of_error_headroom
#print axioms horner_error_recurrence
#print axioms hornerErrorBudget_closed_form
#print axioms horner_error_unit_interval
#print axioms horner_two_step

end CodeLib.Numerical
