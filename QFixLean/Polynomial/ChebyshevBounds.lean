module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic.FieldSimp

/-!
# Bounds for normalized Chebyshev ratios

Reference: Yoder, Low, Chuang, *Fixed-point quantum search with an optimal
number of queries*, arXiv:1409.3305v2, equation (1) and its following interval
argument. These are scalar polynomial facts, independent of an algorithm.

`evalT` is exactly evaluation of Mathlib's first-kind Chebyshev polynomial,
with a natural degree embedded into its integer index. `amplitude` is signed;
only its absolute value is bounded. Denominator bounds hold at every natural
degree, including zero, without an oddness condition.
-/

@[expose] public section

namespace QFixLean.Chebyshev

noncomputable section

/-- Evaluation of Mathlib's first-kind Chebyshev polynomial at a natural degree. -/
def evalT (L : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval x

/-- The normalization denominator for a positive scale `γ ≤ 1`. -/
def denominator (L : ℕ) (γ : ℝ) : ℝ := evalT L (1 / γ)

/-- A signed scalar ratio; division is meaningful for the bounds below because
their hypotheses imply that the denominator is positive. -/
def amplitude (L : ℕ) (γ x : ℝ) : ℝ := evalT L (x / γ) / denominator L γ

@[simp]
theorem evalT_one (x : ℝ) : evalT 1 x = x := by
  simp [evalT]

@[simp]
theorem evalT_at_one (L : ℕ) : evalT L 1 = 1 := by
  simp [evalT]

theorem one_le_inv_scale {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) : 1 ≤ 1 / γ :=
  (one_le_div hγ).2 hγ1

theorem denominator_ge_one (L : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    1 ≤ denominator L γ :=
  Polynomial.Chebyshev.one_le_eval_T_real (L : ℤ) (one_le_inv_scale hγ hγ1)

theorem denominator_pos (L : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 < denominator L γ :=
  lt_of_lt_of_le zero_lt_one (denominator_ge_one L hγ hγ1)

theorem denominator_ne_zero (L : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    denominator L γ ≠ 0 := (denominator_pos L hγ hγ1).ne'

theorem abs_div_scale_le_one {γ x : ℝ} (hγ : 0 < γ) (hx : |x| ≤ γ) :
    |x / γ| ≤ 1 := by
  rw [abs_div, abs_of_pos hγ]
  exact (div_le_one hγ).2 hx

/-- Mathlib's interval bound applied to the scaled input. -/
theorem abs_evalT_div_le_one (L : ℕ) {γ x : ℝ} (hγ : 0 < γ) (hx : |x| ≤ γ) :
    |evalT L (x / γ)| ≤ 1 :=
  Polynomial.Chebyshev.abs_eval_T_real_le_one (L : ℤ) (abs_div_scale_le_one hγ hx)

/-- The normalization denominator is derived from `0 < γ ≤ 1`, rather than
assumed to be nonzero or to satisfy the desired error bound. -/
theorem abs_amplitude_le (L : ℕ) {γ x : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hx : |x| ≤ γ) : |amplitude L γ x| ≤ 1 / denominator L γ := by
  rw [amplitude, abs_div, abs_of_pos (denominator_pos L hγ hγ1)]
  exact div_le_div_of_nonneg_right (abs_evalT_div_le_one L hγ hx)
    (denominator_pos L hγ hγ1).le

/-- Degree one retains the input scalar exactly, for every nonzero scale. -/
theorem amplitude_one {γ : ℝ} (hγ : γ ≠ 0) (x : ℝ) : amplitude 1 γ x = x := by
  simp only [amplitude, denominator, evalT_one]
  field_simp

end
end QFixLean.Chebyshev
