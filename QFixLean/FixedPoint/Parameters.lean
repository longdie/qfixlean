module

public import QFixLean.Polynomial.ChebyshevParameters
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite degree selection for fixed-point search

P14, arXiv:1409.3305v2, degree condition (3): a sufficient degree scales as
`log (2/δ) / sqrt λ₀`. Here λ₀ is a success probability, whereas P24,
arXiv:2403.02057v3, Section 3.3 uses an amplitude lower bound. All estimates
below are finite inequalities, with a specified odd rounding rule.
-/

@[expose] public section

namespace QFixLean.FixedPoint.Parameters

noncomputable section

/-- The real sufficient-degree bound; δ bounds failure amplitude. -/
def bound (lam₀ δ : ℝ) : ℝ := Real.log (2 / δ) / Real.sqrt lam₀

/-- Conservative explicit number of generalized iterations. -/
def iterations (lam₀ δ : ℝ) : ℕ := ⌈bound lam₀ δ / 2⌉₊

/-- The positive odd polynomial degree selected by the algorithm. -/
def degree (lam₀ δ : ℝ) : ℕ := 2 * iterations lam₀ δ + 1

/-- The oracle count of the compiled construction is later proved to equal this. -/
def queries (lam₀ δ : ℝ) : ℕ := 2 * iterations lam₀ δ

/-- Elementary hyperbolic comparison, proved by differentiating
`t cosh t - sinh t` on the nonnegative half-line. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  have hd (x : ℝ) : HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
      (x * Real.sinh x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    · rfl
    · dsimp
      ring
  have hm : MonotoneOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact (continuous_id.mul Real.continuous_cosh |>.sub Real.continuous_sinh).continuousOn
    · intro x _
      exact (hd x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact mul_nonneg hx.le (Real.sinh_nonneg_iff.mpr hx.le)
  have h := hm (by simp) ht ht
  have hh : 0 ≤ t * Real.cosh t - Real.sinh t := by simpa using h
  linarith

/-- The width identity is exact, without a small-angle approximation. -/
theorem width_eq_tanh_sq (t : ℝ) :
    1 - (1 / Real.cosh t) ^ 2 = Real.tanh t ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos t
  have h := Real.cosh_sq_sub_sinh_sq t
  field_simp
  nlinarith

/-- `0 ≤ tanh t ≤ t` for a nonnegative argument. -/
theorem tanh_bounds {t : ℝ} (ht : 0 ≤ t) : Real.tanh t ∈ Set.Icc 0 t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact ⟨div_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.cosh_pos t).le,
    (div_le_iff₀ (Real.cosh_pos t)).mpr (sinh_le_mul_cosh ht)⟩

/-- The inverse-hyperbolic numerator is at most the logarithmic numerator. -/
theorem arcosh_le_log {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.arcosh (1 / δ) ≤ Real.log (2 / δ) := by
  have hx : 1 < 1 / δ := (one_lt_div hδ).mpr hδ1
  have hs : Real.sqrt ((1 / δ) ^ 2 - 1) ≤ 1 / δ := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by linarith⟩
  unfold Real.arcosh
  apply Real.log_le_log (by positivity)
  calc
    1 / δ + Real.sqrt ((1 / δ) ^ 2 - 1) ≤ 1 / δ + 1 / δ := by linarith
    _ = 2 / δ := by ring

theorem bound_pos {lam₀ δ : ℝ} (hlam₀ : 0 < lam₀)
    (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < bound lam₀ δ := by
  apply div_pos _ (Real.sqrt_pos.mpr hlam₀)
  apply Real.log_pos
  exact (one_lt_div hδ).mpr (by linarith)

/-- A real lower bound on the positive degree discharges the parameter
matching hypothesis used by M17. No amplitude formula is assumed. -/
theorem sufficient_degree {L : ℕ} {lam₀ δ : ℝ} (hL : 0 < L)
    (hlam₀ : 0 < lam₀) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdegree : bound lam₀ δ ≤ (L : ℝ)) :
    1 - (Chebyshev.parameter L δ) ^ 2 ≤ lam₀ := by
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hs : 0 < Real.sqrt lam₀ := Real.sqrt_pos.mpr hlam₀
  have ha : 0 ≤ Real.arcosh (1 / δ) :=
    Real.arcosh_nonneg ((one_lt_div hδ).mpr hδ1).le
  have ht : 0 ≤ Real.arcosh (1 / δ) / (L : ℝ) := div_nonneg ha hLr.le
  have hlog : Real.log (2 / δ) ≤ (L : ℝ) * Real.sqrt lam₀ := by
    exact (div_le_iff₀ hs).mp hdegree
  have htbound : Real.arcosh (1 / δ) / (L : ℝ) ≤ Real.sqrt lam₀ := by
    apply (div_le_iff₀ hLr).mpr
    nlinarith [arcosh_le_log hδ hδ1]
  rw [Chebyshev.parameter, width_eq_tanh_sq]
  have htan := tanh_bounds ht
  have hroot := Real.sq_sqrt hlam₀.le
  have hh := htan.2.trans htbound
  nlinarith [htan.1]

@[simp] theorem degree_pos (lam₀ δ : ℝ) : 0 < degree lam₀ δ := by
  unfold degree
  omega

theorem degree_odd (lam₀ δ : ℝ) : Odd (degree lam₀ δ) :=
  ⟨iterations lam₀ δ, rfl⟩

/-- The rounded odd degree always dominates the real bound. -/
theorem bound_le_degree (lam₀ δ : ℝ) : bound lam₀ δ ≤ (degree lam₀ δ : ℝ) := by
  have h := Nat.le_ceil (bound lam₀ δ / 2)
  dsimp [degree, iterations]
  push_cast
  linarith

/-- The selected standard parameter matches the supplied lower success bound. -/
theorem parameter_match {lam₀ δ : ℝ} (hlam₀ : 0 < lam₀)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - (Chebyshev.parameter (degree lam₀ δ) δ) ^ 2 ≤ lam₀ :=
  sufficient_degree (degree_pos _ _) hlam₀ hδ hδ1 (bound_le_degree _ _)

@[simp] theorem queries_eq_degree_sub_one (lam₀ δ : ℝ) :
    queries lam₀ δ = degree lam₀ δ - 1 := by
  simp [queries, degree]

/-- An explicit finite oracle-query upper bound, with additive rounding cost. -/
theorem queries_lt_bound_add_two {lam₀ δ : ℝ} (hlam₀ : 0 < lam₀)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    (queries lam₀ δ : ℝ) < bound lam₀ δ + 2 := by
  have h := Nat.ceil_lt_add_one (div_nonneg (bound_pos hlam₀ hδ hδ1).le (by norm_num : (0 : ℝ) ≤ 2))
  dsimp [queries, iterations]
  push_cast
  linarith

theorem degree_lt_bound_add_three {lam₀ δ : ℝ} (hlam₀ : 0 < lam₀)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    (degree lam₀ δ : ℝ) < bound lam₀ δ + 3 := by
  have h := queries_lt_bound_add_two hlam₀ hδ hδ1
  dsimp [queries, degree] at *
  push_cast at *
  linarith

/-- The same finite matching theorem includes a unit success promise. -/
theorem parameter_match_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - (Chebyshev.parameter (degree 1 δ) δ) ^ 2 ≤ 1 :=
  parameter_match (by norm_num) hδ hδ1

/-- Exact rounding for the joint rational-state example. The logarithm bounds
are symbolic consequences of `exp 1 < 3` and `log 2 < 1`. -/
theorem iterations_quarter_half : iterations (1 / 4) (1 / 2) = 2 := by
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hlower : 1 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.exp_one_lt_three]
  have hupper : Real.log 4 < 2 := by
    rw [Real.log_four_eq]
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  rw [iterations, Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)]
  norm_num [bound, hsqrt]
  constructor <;> nlinarith

@[simp] theorem degree_quarter_half : degree (1 / 4) (1 / 2) = 5 := by
  rw [degree, iterations_quarter_half]

@[simp] theorem queries_quarter_half : queries (1 / 4) (1 / 2) = 4 := by
  rw [queries, iterations_quarter_half]

end
end QFixLean.FixedPoint.Parameters
