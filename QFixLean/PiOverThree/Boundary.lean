module

public import QFixLean.PiOverThree.Recursion
import Mathlib.Tactic.Linarith

/-!
# Endpoint behavior of recursive π/3 search

The actual recursive output remains in the target if its initial failure
probability is zero, and remains orthogonal to the target if that probability
is one. These conclusions concern projection components and probabilities;
they do not assert equality of phase-retaining output vectors at different
levels. The closed form is from P05 v1, Section 4, following equation (4).
-/

@[expose] public section

namespace QFixLean.PiOverThree

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Initial failure zero is exactly initial success one. -/
theorem initial_failureWeight_eq_zero_iff (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    failureWeight P ((U : E →L[ℂ] E) (s : E)) = 0 ↔
      successWeight P ((U : E →L[ℂ] E) (s : E)) = 1 := by
  have h := successWeight_add_failureWeight_of_norm_eq_one hP
    (searchRecursion_normalized U s hP 0)
  simp only [searchRecursion_zero] at h
  constructor <;> intro h0 <;> linarith

/-- Initial failure one is exactly initial success zero. -/
theorem initial_failureWeight_eq_one_iff (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    failureWeight P ((U : E →L[ℂ] E) (s : E)) = 1 ↔
      successWeight P ((U : E →L[ℂ] E) (s : E)) = 0 := by
  have h := successWeight_add_failureWeight_of_norm_eq_one hP
    (searchRecursion_normalized U s hP 0)
  simp only [searchRecursion_zero] at h
  constructor <;> intro h1 <;> linarith

/-- The convergence condition can equivalently be stated as positive initial
success probability. It includes initial failure zero. -/
theorem initial_failureWeight_lt_one_iff (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    failureWeight P ((U : E →L[ℂ] E) (s : E)) < 1 ↔
      0 < successWeight P ((U : E →L[ℂ] E) (s : E)) := by
  have h := successWeight_add_failureWeight_of_norm_eq_one hP
    (searchRecursion_normalized U s hP 0)
  simp only [searchRecursion_zero] at h
  constructor <;> intro hlt <;> linarith

/-- An initially successful preparation has no failure at any level. -/
theorem searchRecursion_failureWeight_eq_zero (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (h0 : failureWeight P ((U : E →L[ℂ] E) (s : E)) = 0) (k : ℕ) :
    failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) = 0 := by
  rw [searchRecursion_failureWeight, h0, zero_pow (pow_ne_zero k (by decide))]

theorem searchRecursion_successWeight_eq_one (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (h0 : failureWeight P ((U : E →L[ℂ] E) (s : E)) = 0) (k : ℕ) :
    successWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) = 1 := by
  rw [searchRecursion_successWeight, h0, zero_pow (pow_ne_zero k (by decide)), sub_zero]

/-- Probability one means the actual output has zero complementary component;
it does not imply that successive output vectors have equal global phase. -/
theorem searchRecursion_complement_eq_zero (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (h0 : failureWeight P ((U : E →L[ℂ] E) (s : E)) = 0) (k : ℕ) :
    (1 - P) ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) = 0 := by
  simpa only [failureWeight, sq_eq_zero_iff, norm_eq_zero] using
    searchRecursion_failureWeight_eq_zero U s hP h0 k

/-- Without an initial target component, the recursion cannot create success. -/
theorem searchRecursion_failureWeight_eq_one (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (h1 : failureWeight P ((U : E →L[ℂ] E) (s : E)) = 1) (k : ℕ) :
    failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) = 1 := by
  rw [searchRecursion_failureWeight, h1, one_pow]

theorem searchRecursion_successWeight_eq_zero (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (h1 : failureWeight P ((U : E →L[ℂ] E) (s : E)) = 1) (k : ℕ) :
    successWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) = 0 := by
  rw [searchRecursion_successWeight, h1, one_pow, sub_self]

/-- The actual target projection is zero at every level in the failure-one
endpoint, while the full normalized vector need not remain unchanged. -/
theorem searchRecursion_target_eq_zero (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (h1 : failureWeight P ((U : E →L[ℂ] E) (s : E)) = 1) (k : ℕ) :
    P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) = 0 := by
  simpa only [successWeight, sq_eq_zero_iff, norm_eq_zero] using
    searchRecursion_successWeight_eq_zero U s hP h1 k

end
end QFixLean.PiOverThree
