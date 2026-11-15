module

public import QFixLean.PiOverThree.Boundary
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# Monotonicity and convergence of recursive π/3 search

Reference: Grover, *A different kind of quantum search*, quant-ph/0503205v1,
Section 4, the probability formula following equation (4), and Section 4.1.

All sequences below measure the actual output of `searchRecursion` on the
fixed original source. Failure probabilities are nonincreasing, including both endpoints.
When the initial failure probability is less than one, failure and the norm
of the complementary component tend to zero, and success tends to one.
These statements do not assert convergence of the phase-retaining state vector
or a query complexity bound.
-/

@[expose] public section

namespace QFixLean.PiOverThree

noncomputable section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem searchRecursion_failureWeight_mem_Icc (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) ∈
      Set.Icc (0 : ℝ) 1 :=
  failureWeight_mem_Icc_of_norm_eq_one hP (searchRecursion_normalized U s hP k)

theorem searchRecursion_successWeight_mem_Icc (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    successWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) ∈
      Set.Icc (0 : ℝ) 1 :=
  successWeight_mem_Icc_of_norm_eq_one hP (searchRecursion_normalized U s hP k)

/-- Cubing a probability in `[0,1]` cannot increase it. Both endpoints are allowed. -/
theorem searchRecursion_failureWeight_succ_le (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    failureWeight P ((searchRecursion U s hP (k + 1) : E →L[ℂ] E) (s : E)) ≤
      failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) := by
  rw [searchRecursion_failureWeight_succ]
  have h := searchRecursion_failureWeight_mem_Icc U s hP k
  let e := failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E))
  change e ^ 3 ≤ e
  calc
    e ^ 3 = e ^ 2 * e := pow_succ _ _
    _ ≤ e ^ 2 * 1 := mul_le_mul_of_nonneg_left h.2 (sq_nonneg e)
    _ ≤ e := by nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]

theorem searchRecursion_failureWeight_antitone (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    Antitone (fun k : ℕ =>
      failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E))) :=
  antitone_nat_of_succ_le (searchRecursion_failureWeight_succ_le U s hP)

/-- Success is nondecreasing for the same normalized outputs whose failure is nonincreasing. -/
theorem searchRecursion_successWeight_monotone (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    Monotone (fun k : ℕ =>
      successWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E))) := by
  intro i j hij
  have hf := searchRecursion_failureWeight_antitone U s hP hij
  have hi := successWeight_add_failureWeight_of_norm_eq_one hP
    (searchRecursion_normalized U s hP i)
  have hj := successWeight_add_failureWeight_of_norm_eq_one hP
    (searchRecursion_normalized U s hP j)
  linarith

/-- The exponent `3^k` tends to infinity; the initial failure may equal zero. -/
theorem searchRecursion_failureWeight_tendsto_zero (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (hlt : failureWeight P ((U : E →L[ℂ] E) (s : E)) < 1) :
    Tendsto (fun k : ℕ =>
      failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)))
      atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (failureWeight_nonneg P ((U : E →L[ℂ] E) (s : E))) hlt
  have he : Tendsto (fun k : ℕ => (3 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  simpa only [Function.comp_def, searchRecursion_failureWeight] using hp.comp he

theorem searchRecursion_successWeight_tendsto_one (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (hlt : failureWeight P ((U : E →L[ℂ] E) (s : E)) < 1) :
    Tendsto (fun k : ℕ =>
      successWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)))
      atTop (𝓝 1) := by
  have hf := searchRecursion_failureWeight_tendsto_zero U s hP hlt
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hf
  simpa only [searchRecursion_successWeight, searchRecursion_failureWeight, sub_zero]
    using h

/-- The complementary norm, rather than a phase-retaining full vector, tends to zero. -/
theorem searchRecursion_complement_norm_tendsto_zero (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (hlt : failureWeight P ((U : E →L[ℂ] E) (s : E)) < 1) :
    Tendsto (fun k : ℕ =>
      ‖(1 - P) ((searchRecursion U s hP k : E →L[ℂ] E) (s : E))‖)
      atTop (𝓝 0) := by
  have h := (searchRecursion_failureWeight_tendsto_zero U s hP hlt).sqrt
  simpa only [failureWeight, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end
end QFixLean.PiOverThree
