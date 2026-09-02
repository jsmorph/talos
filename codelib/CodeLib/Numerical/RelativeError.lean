import Mathlib.Tactic

/-!
# Relative-error accumulation

Format-independent real inequalities for turning repeated local relative-error
factors into the standard `gamma` bound.  Floating-point operation theorems
provide the local hypotheses; this module only performs transparent real
algebra.
-/

namespace CodeLib.Numerical

/-- One multiplicative relative-error step with unit roundoff `u`. -/
def unitStepFactor (u : ℝ) : ℝ := 1 + u

/-- The standard accumulated relative-error factor
`gamma k u = k * u / (1 - k * u)`. -/
noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

theorem unitStepFactor_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ unitStepFactor u := by
  unfold unitStepFactor
  linarith

theorem unitStepFactor_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unitStepFactor u := by
  unfold unitStepFactor
  linarith

theorem gamma_denominator_pos {k : ℕ} {u : ℝ}
    (hku : (k : ℝ) * u < 1) :
    0 < 1 - (k : ℝ) * u :=
  sub_pos.mpr hku

theorem gamma_zero (u : ℝ) : gamma 0 u = 0 := by
  simp [gamma]

theorem gamma_nonneg {k : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1) :
    0 ≤ gamma k u := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hu)
    (le_of_lt (gamma_denominator_pos hku))

/-- `1 + gamma k u` is the reciprocal of the remaining error headroom. -/
theorem one_add_gamma {k : ℕ} {u : ℝ}
    (hku : (k : ℝ) * u < 1) :
    1 + gamma k u = 1 / (1 - (k : ℝ) * u) := by
  unfold gamma
  field_simp [ne_of_gt (gamma_denominator_pos hku)]
  ring

/-- The fractional-linear function used by `gamma` is monotone below its
pole at one. -/
theorem ratio_one_sub_mono {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) :
    x / (1 - x) ≤ y / (1 - y) := by
  have hxden : 0 < 1 - x := sub_pos.mpr (hxy.trans_lt hy)
  have hyden : 0 < 1 - y := sub_pos.mpr hy
  apply (div_le_div_iff₀ hxden hyden).2
  calc
    x * (1 - y) = x - x * y := by ring
    _ ≤ y - y * x := by
      rw [mul_comm y x]
      exact sub_le_sub_right hxy (x * y)
    _ = y * (1 - x) := by ring

/-- Increasing the number of rounding steps can only increase `gamma`, while
the larger index remains below the pole. -/
theorem gamma_mono_steps {k m : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hkm : k ≤ m) (hmu : (m : ℝ) * u < 1) :
    gamma k u ≤ gamma m u := by
  unfold gamma
  apply ratio_one_sub_mono
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) hu
  · exact hmu

/-- Increasing the admitted unit roundoff can only increase `gamma`, while
the larger roundoff remains below the pole. -/
theorem gamma_mono_roundoff {k : ℕ} {u v : ℝ}
    (huv : u ≤ v) (hkv : (k : ℝ) * v < 1) :
    gamma k u ≤ gamma k v := by
  unfold gamma
  apply ratio_one_sub_mono
  · exact mul_le_mul_of_nonneg_left huv (Nat.cast_nonneg k)
  · exact hkv

/-- Repeated `1 + u` factors are bounded by the reciprocal remaining
headroom.  This is the algebraic core of the standard `gamma` estimate. -/
theorem unitStepFactor_pow_le_inv (k : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1) :
    unitStepFactor u ^ k ≤ 1 / (1 - (k : ℝ) * u) := by
  induction k with
  | zero => norm_num [unitStepFactor]
  | succ k ih =>
      have hkcast : (k : ℝ) ≤ (Nat.succ k : ℕ) := by
        exact_mod_cast Nat.le_succ k
      have hkule : (k : ℝ) * u ≤ (Nat.succ k : ℕ) * u :=
        mul_le_mul_of_nonneg_right hkcast hu
      have hku' : (k : ℝ) * u < 1 := hkule.trans_lt hku
      have hkden : 0 < 1 - (k : ℝ) * u := gamma_denominator_pos hku'
      have hsuccden : 0 < 1 - (Nat.succ k : ℕ) * u :=
        gamma_denominator_pos hku
      calc
        unitStepFactor u ^ Nat.succ k =
            unitStepFactor u ^ k * unitStepFactor u := by rw [pow_succ]
        _ ≤ (1 / (1 - (k : ℝ) * u)) * unitStepFactor u :=
          mul_le_mul_of_nonneg_right (ih hku') (unitStepFactor_nonneg hu)
        _ = unitStepFactor u / (1 - (k : ℝ) * u) := by ring
        _ ≤ 1 / (1 - (Nat.succ k : ℕ) * u) := by
          apply (div_le_div_iff₀ hkden hsuccden).2
          unfold unitStepFactor
          rw [Nat.cast_succ]
          have hnonneg : 0 ≤ ((k : ℝ) + 1) * u ^ 2 :=
            mul_nonneg (by positivity) (sq_nonneg u)
          nlinarith

/-- The direct repeated-factor error is bounded by the standard `gamma`
factor whenever `k * u < 1`. -/
theorem unitStepFactor_pow_sub_one_le_gamma (k : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1) :
    unitStepFactor u ^ k - 1 ≤ gamma k u := by
  have hpow := unitStepFactor_pow_le_inv k hu hku
  have hgamma := one_add_gamma hku
  linarith

theorem unitStepFactor_pow_le_one_add_gamma (k : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1) :
    unitStepFactor u ^ k ≤ 1 + gamma k u := by
  linarith [unitStepFactor_pow_sub_one_le_gamma k hu hku]

/-- Multiplying the repeated-factor estimate by a nonnegative magnitude
budget preserves the `gamma` bound. -/
theorem geometric_error_le_gamma_mul (k : ℕ) {u magnitude : ℝ}
    (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1)
    (hmagnitude : 0 ≤ magnitude) :
    (unitStepFactor u ^ k - 1) * magnitude ≤
      gamma k u * magnitude := by
  exact mul_le_mul_of_nonneg_right
    (unitStepFactor_pow_sub_one_le_gamma k hu hku) hmagnitude

/-- A convenient final step for clients that first prove the sharper
geometric-factor estimate. -/
theorem relative_error_le_gamma_mul {error magnitude u : ℝ} {k : ℕ}
    (herror : |error| ≤ (unitStepFactor u ^ k - 1) * magnitude)
    (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1)
    (hmagnitude : 0 ≤ magnitude) :
    |error| ≤ gamma k u * magnitude :=
  herror.trans (geometric_error_le_gamma_mul k hu hku hmagnitude)

/-! ## Sequential modeled dot products -/

/-- One product rounding followed by one addition rounding advances a
geometric relative-error budget by two operations. -/
theorem relative_mul_add_step_geometric {u approximate exact term
    roundedTerm output magnitude : ℝ} {k : ℕ}
    (hu : 0 ≤ u)
    (hexact : |exact| ≤ magnitude)
    (hprevious :
      |approximate - exact| ≤
        (unitStepFactor u ^ k - 1) * magnitude)
    (hterm : |roundedTerm - term| ≤ u * |term|)
    (haddition :
      |output - (approximate + roundedTerm)| ≤
        u * |approximate + roundedTerm|) :
    |output - (exact + term)| ≤
      (unitStepFactor u ^ (k + 2) - 1) * (magnitude + |term|) := by
  have hmagnitude : 0 ≤ magnitude := (abs_nonneg exact).trans hexact
  have hfactor : 1 ≤ unitStepFactor u := by
    simp only [unitStepFactor]
    linarith
  have happroximate :
      |approximate| ≤
        magnitude + (unitStepFactor u ^ k - 1) * magnitude := by
    rw [show approximate = (approximate - exact) + exact by ring]
    calc
      |approximate - exact + exact| ≤
          |approximate - exact| + |exact| := abs_add_le _ _
      _ ≤ (unitStepFactor u ^ k - 1) * magnitude + magnitude :=
        add_le_add hprevious hexact
      _ = magnitude + (unitStepFactor u ^ k - 1) * magnitude := by ring
  have hroundedTerm : |roundedTerm| ≤ (1 + u) * |term| := by
    rw [show roundedTerm = (roundedTerm - term) + term by ring]
    calc
      |roundedTerm - term + term| ≤ |roundedTerm - term| + |term| :=
        abs_add_le _ _
      _ ≤ u * |term| + |term| := add_le_add hterm (le_refl _)
      _ = (1 + u) * |term| := by ring
  have hsumMagnitude :
      |approximate + roundedTerm| ≤
        magnitude + (unitStepFactor u ^ k - 1) * magnitude +
          unitStepFactor u * |term| := by
    calc
      |approximate + roundedTerm| ≤ |approximate| + |roundedTerm| :=
        abs_add_le _ _
      _ ≤ (magnitude + (unitStepFactor u ^ k - 1) * magnitude) +
          ((1 + u) * |term|) := add_le_add happroximate hroundedTerm
      _ = magnitude + (unitStepFactor u ^ k - 1) * magnitude +
          unitStepFactor u * |term| := by rfl
  have hraw :
      |output - (exact + term)| ≤
        u * (magnitude + (unitStepFactor u ^ k - 1) * magnitude +
          unitStepFactor u * |term|) +
        (unitStepFactor u ^ k - 1) * magnitude + u * |term| := by
    rw [show output - (exact + term) =
      (output - (approximate + roundedTerm)) +
        (approximate - exact) + (roundedTerm - term) by ring]
    calc
      |(output - (approximate + roundedTerm)) +
          (approximate - exact) + (roundedTerm - term)| ≤
        |output - (approximate + roundedTerm)| +
            |approximate - exact| + |roundedTerm - term| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ u * |approximate + roundedTerm| +
            (unitStepFactor u ^ k - 1) * magnitude + u * |term| := by
          exact add_le_add (add_le_add haddition hprevious) hterm
      _ ≤ u * (magnitude + (unitStepFactor u ^ k - 1) * magnitude +
            unitStepFactor u * |term|) +
            (unitStepFactor u ^ k - 1) * magnitude + u * |term| := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left hsumMagnitude hu)
              (le_refl _))
            (le_refl _)
  have hpowK1 :
      unitStepFactor u ^ (k + 1) ≤ unitStepFactor u ^ (k + 2) :=
    pow_le_pow_right₀ hfactor (by omega)
  have hpow2 :
      unitStepFactor u ^ 2 ≤ unitStepFactor u ^ (k + 2) :=
    pow_le_pow_right₀ hfactor (by omega)
  refine hraw.trans ?_
  have hcoeffMagnitude :
      unitStepFactor u ^ (k + 1) - 1 ≤
        unitStepFactor u ^ (k + 2) - 1 := sub_le_sub_right hpowK1 1
  have hcoeffTerm :
      unitStepFactor u ^ 2 - 1 ≤
        unitStepFactor u ^ (k + 2) - 1 := sub_le_sub_right hpow2 1
  calc
    u * (magnitude + (unitStepFactor u ^ k - 1) * magnitude +
          unitStepFactor u * |term|) +
        (unitStepFactor u ^ k - 1) * magnitude + u * |term| =
      (unitStepFactor u ^ (k + 1) - 1) * magnitude +
        (unitStepFactor u ^ 2 - 1) * |term| := by
          simp only [unitStepFactor, pow_succ]
          ring
    _ ≤ (unitStepFactor u ^ (k + 2) - 1) * magnitude +
          (unitStepFactor u ^ (k + 2) - 1) * |term| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoeffMagnitude hmagnitude)
        (mul_le_mul_of_nonneg_right hcoeffTerm (abs_nonneg term))
    _ = (unitStepFactor u ^ (k + 2) - 1) *
          (magnitude + |term|) := by ring

/-- Exact sequential accumulation of real-valued product terms. -/
def sequentialExactSum : ℝ → List ℝ → ℝ
  | accumulator, [] => accumulator
  | accumulator, term :: terms =>
      sequentialExactSum (accumulator + term) terms

/-- The corresponding sum-of-magnitudes accumulator. -/
def sequentialMagnitude : ℝ → List ℝ → ℝ
  | magnitude, [] => magnitude
  | magnitude, term :: terms =>
      sequentialMagnitude (magnitude + |term|) terms

theorem sequentialExactSum_eq_add_sum (accumulator : ℝ) (terms : List ℝ) :
    sequentialExactSum accumulator terms = accumulator + terms.sum := by
  induction terms generalizing accumulator with
  | nil => simp [sequentialExactSum]
  | cons term terms ih =>
      simp only [sequentialExactSum, List.sum_cons, ih]
      ring

theorem sequentialMagnitude_eq_add_sum_abs (magnitude : ℝ)
    (terms : List ℝ) :
    sequentialMagnitude magnitude terms =
      magnitude + (terms.map fun term => |term|).sum := by
  induction terms generalizing magnitude with
  | nil => simp [sequentialMagnitude]
  | cons term terms ih =>
      simp only [sequentialMagnitude, List.map_cons, List.sum_cons, ih]
      ring

/-- A sequential dot-product trace in the standard relative-error model.
Each stage rounds one exact product term and then rounds its addition to the
current approximate accumulator. -/
inductive RelativeDotAcc (u : ℝ) : ℝ → List ℝ → ℝ → Prop
  | nil (accumulator : ℝ) : RelativeDotAcc u accumulator [] accumulator
  | cons {accumulator term roundedTerm rounded output : ℝ}
      {terms : List ℝ}
      (hterm : |roundedTerm - term| ≤ u * |term|)
      (haddition :
        |rounded - (accumulator + roundedTerm)| ≤
          u * |accumulator + roundedTerm|)
      (tail : RelativeDotAcc u rounded terms output) :
      RelativeDotAcc u accumulator (term :: terms) output

theorem sequentialMagnitude_nonneg {magnitude : ℝ} (terms : List ℝ)
    (hmagnitude : 0 ≤ magnitude) :
    0 ≤ sequentialMagnitude magnitude terms := by
  induction terms generalizing magnitude with
  | nil => simpa [sequentialMagnitude] using hmagnitude
  | cons term terms ih =>
      simp only [sequentialMagnitude]
      exact ih (add_nonneg hmagnitude (abs_nonneg term))

/-- A trace starting after `k` relative-error operations satisfies a uniform
geometric-factor bound after two further operations per product term. -/
theorem relativeDotAcc_geometric_error {u approximate exact magnitude output : ℝ}
    {k : ℕ} {terms : List ℝ}
    (hu : 0 ≤ u)
    (hexact : |exact| ≤ magnitude)
    (hprevious :
      |approximate - exact| ≤
        (unitStepFactor u ^ k - 1) * magnitude)
    (htrace : RelativeDotAcc u approximate terms output) :
    |output - sequentialExactSum exact terms| ≤
      (unitStepFactor u ^ (k + 2 * terms.length) - 1) *
        sequentialMagnitude magnitude terms := by
  induction htrace generalizing exact magnitude k with
  | nil accumulator =>
      simpa [sequentialExactSum, sequentialMagnitude] using hprevious
  | @cons accumulator term roundedTerm rounded output terms
      hterm haddition tail ih =>
      have hstep := relative_mul_add_step_geometric hu hexact hprevious
        hterm haddition
      have hexactNext : |exact + term| ≤ magnitude + |term| := by
        exact (abs_add_le _ _).trans (add_le_add hexact (le_refl _))
      have htail := ih hexactNext hstep
      simp only [sequentialExactSum, sequentialMagnitude, List.length_cons]
      rw [← show k + 2 + 2 * terms.length =
        k + 2 * (terms.length + 1) by omega]
      exact htail

/-- A nonempty modeled dot product is bounded by `gamma_(2n-1)` times the
sum of exact product magnitudes. -/
theorem relativeDotAcc_gamma_error {u first roundedFirst output : ℝ}
    {terms : List ℝ}
    (hu : 0 ≤ u)
    (hku : (((2 * terms.length + 1 : ℕ) : ℝ) * u) < 1)
    (hfirst : |roundedFirst - first| ≤ u * |first|)
    (htrace : RelativeDotAcc u roundedFirst terms output) :
    |output - sequentialExactSum first terms| ≤
      gamma (2 * terms.length + 1) u *
        sequentialMagnitude |first| terms := by
  have hfirstGeometric :
      |roundedFirst - first| ≤
        (unitStepFactor u ^ 1 - 1) * |first| := by
    simpa [unitStepFactor] using hfirst
  have hgeometric := relativeDotAcc_geometric_error hu
    (magnitude := |first|) (k := 1) (le_refl |first|)
    hfirstGeometric htrace
  have hexponent : 1 + 2 * terms.length = 2 * terms.length + 1 := by omega
  rw [hexponent] at hgeometric
  exact relative_error_le_gamma_mul hgeometric hu hku
    (sequentialMagnitude_nonneg terms (abs_nonneg first))

#print axioms gamma_nonneg
#print axioms one_add_gamma
#print axioms ratio_one_sub_mono
#print axioms gamma_mono_steps
#print axioms gamma_mono_roundoff
#print axioms unitStepFactor_pow_le_inv
#print axioms unitStepFactor_pow_sub_one_le_gamma
#print axioms unitStepFactor_pow_le_one_add_gamma
#print axioms geometric_error_le_gamma_mul
#print axioms relative_error_le_gamma_mul
#print axioms relative_mul_add_step_geometric
#print axioms sequentialExactSum_eq_add_sum
#print axioms sequentialMagnitude_eq_add_sum_abs
#print axioms relativeDotAcc_geometric_error
#print axioms relativeDotAcc_gamma_error

end CodeLib.Numerical
