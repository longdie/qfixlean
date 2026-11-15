module

public import QFixLean.PiOverThree.Recursion
public import QFixLean.Examples.PiOverThree
import Mathlib.Tactic.NormNum

/-!
# Exact π/3 recursion examples

For identity preparation of `(3/5, 4/5)` and the first-coordinate target,
the first three failure probabilities are `16/25`, `(16/25)^3` and `(16/25)^9`.
The second recursive layer is checked both by applying the single-step
theorem twice and by specializing the recursive closed form.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

theorem rationalState_searchRecursion_zero_failure :
    failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection 0 :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (16 / 25 : ℝ) := by
  change failureWeight firstBasisTarget (rationalState : QubitSpace) = _
  exact rationalState_failure

/-- The first recursive layer is exactly the previously verified M07 output. -/
theorem rationalState_searchRecursion_one_failure :
    failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection 1 :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (4096 / 15625 : ℝ) := by
  change failureWeight firstBasisTarget
    ((PiOverThree.searchStep 1 rationalState firstBasisTarget_isStarProjection :
      QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = _
  exact rationalState_searchStep_failure

/-- Expand both recursive layers and use only the M07 single-step cubing theorem,
without the recursive probability recurrence or its closed-form theorem. -/
theorem rationalState_searchRecursion_two_failure_steps :
    failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection 2 :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (16 / 25 : ℝ) ^ 9 := by
  rw [PiOverThree.searchRecursion_succ, PiOverThree.searchStep_failureWeight,
    PiOverThree.searchRecursion_succ, PiOverThree.searchStep_failureWeight,
    PiOverThree.searchRecursion_zero]
  change (failureWeight firstBasisTarget (rationalState : QubitSpace) ^ 3) ^ 3 = _
  rw [rationalState_failure, ← pow_mul]

/-- The general recursive closed form gives the same second-layer probability. -/
theorem rationalState_searchRecursion_two_failure :
    failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection 2 :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (16 / 25 : ℝ) ^ 9 := by
  rw [PiOverThree.searchRecursion_failureWeight]
  change failureWeight firstBasisTarget (rationalState : QubitSpace) ^ ((3 : ℕ) ^ 2) = _
  rw [rationalState_failure]
  norm_num

/-- Success is computed for the same actual output, at every recursive layer. -/
theorem rationalState_searchRecursion_success (k : ℕ) :
    successWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      1 - (16 / 25 : ℝ) ^ ((3 : ℕ) ^ k) := by
  rw [PiOverThree.searchRecursion_successWeight]
  change 1 - failureWeight firstBasisTarget (rationalState : QubitSpace) ^ ((3 : ℕ) ^ k) = _
  rw [rationalState_failure]

/-- A three-dimensional target retaining two coordinates uses the same recursion. -/
theorem threeLevelState_searchRecursion_failure (k : ℕ) :
    failureWeight firstTwoTarget
      ((PiOverThree.searchRecursion 1 threeLevelState firstTwoTarget_isStarProjection k :
        ThreeLevelSpace →L[ℂ] ThreeLevelSpace) (threeLevelState : ThreeLevelSpace)) =
      (4 / 9 : ℝ) ^ ((3 : ℕ) ^ k) := by
  rw [PiOverThree.searchRecursion_failureWeight]
  change failureWeight firstTwoTarget (threeLevelState : ThreeLevelSpace) ^ ((3 : ℕ) ^ k) = _
  rw [threeLevelState_failure]

end
end QFixLean.Examples
