module

public import QFixLean.PiOverThree.Convergence
public import QFixLean.Examples.PiOverThreeRecursion
import Mathlib.Tactic.NormNum

/-!
# Exact π/3 boundary and convergence examples

The rational qubit example has initial failure probability `16/25 < 1`.
Its first three actual recursive outputs have ordered failure probabilities
`16/25`, `(16/25)^3` and `(16/25)^9`, and its failure probability and
complementary-component norm tend to zero. A three-dimensional target
retaining two coordinates checks the same limits without a rank-one target.

The computational basis examples keep the endpoint probabilities and the
vanishing projection components explicit. They do not assert vector equality
between different recursive levels, since the exact global phase is retained.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

theorem rationalState_initial_failure_lt_one :
    failureWeight firstBasisTarget
      (((1 : unitary (QubitSpace →L[ℂ] QubitSpace)) : QubitSpace →L[ℂ] QubitSpace)
        (rationalState : QubitSpace)) < 1 := by
  change failureWeight firstBasisTarget (rationalState : QubitSpace) < 1
  rw [rationalState_failure]
  norm_num

/-- The exact values from the first three outputs obey the general antitonicity
theorem, rather than relying only on an independent numerical comparison. -/
theorem rationalState_searchRecursion_first_three_order :
    (16 / 25 : ℝ) ^ 9 ≤ (16 / 25 : ℝ) ^ 3 ∧
      (16 / 25 : ℝ) ^ 3 ≤ (16 / 25 : ℝ) := by
  have h12 := PiOverThree.searchRecursion_failureWeight_antitone
    1 rationalState firstBasisTarget_isStarProjection (show (1 : ℕ) ≤ 2 by decide)
  have h01 := PiOverThree.searchRecursion_failureWeight_antitone
    1 rationalState firstBasisTarget_isStarProjection (show (0 : ℕ) ≤ 1 by decide)
  dsimp only at h12 h01
  have hcube : (4096 / 15625 : ℝ) = (16 / 25 : ℝ) ^ 3 := by norm_num
  rw [rationalState_searchRecursion_two_failure,
    rationalState_searchRecursion_one_failure, hcube] at h12
  rw [rationalState_searchRecursion_one_failure,
    rationalState_searchRecursion_zero_failure, hcube] at h01
  exact ⟨h12, h01⟩

theorem rationalState_searchRecursion_failure_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)))
      Filter.atTop (nhds 0) :=
  PiOverThree.searchRecursion_failureWeight_tendsto_zero
    1 rationalState firstBasisTarget_isStarProjection rationalState_initial_failure_lt_one

theorem rationalState_searchRecursion_success_tendsto_one :
    Filter.Tendsto (fun k : ℕ => successWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)))
      Filter.atTop (nhds 1) :=
  PiOverThree.searchRecursion_successWeight_tendsto_one
    1 rationalState firstBasisTarget_isStarProjection rationalState_initial_failure_lt_one

theorem rationalState_searchRecursion_complement_norm_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => ‖(1 - firstBasisTarget)
      ((PiOverThree.searchRecursion 1 rationalState firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace))‖)
      Filter.atTop (nhds 0) :=
  PiOverThree.searchRecursion_complement_norm_tendsto_zero
    1 rationalState firstBasisTarget_isStarProjection rationalState_initial_failure_lt_one

theorem threeLevelState_initial_failure_lt_one :
    failureWeight firstTwoTarget
      (((1 : unitary (ThreeLevelSpace →L[ℂ] ThreeLevelSpace)) :
        ThreeLevelSpace →L[ℂ] ThreeLevelSpace)
        (threeLevelState : ThreeLevelSpace)) < 1 := by
  change failureWeight firstTwoTarget (threeLevelState : ThreeLevelSpace) < 1
  rw [threeLevelState_failure]
  norm_num

theorem threeLevelState_searchRecursion_failure_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => failureWeight firstTwoTarget
      ((PiOverThree.searchRecursion 1 threeLevelState firstTwoTarget_isStarProjection k :
        ThreeLevelSpace →L[ℂ] ThreeLevelSpace) (threeLevelState : ThreeLevelSpace)))
      Filter.atTop (nhds 0) :=
  PiOverThree.searchRecursion_failureWeight_tendsto_zero
    1 threeLevelState firstTwoTarget_isStarProjection threeLevelState_initial_failure_lt_one

theorem threeLevelState_searchRecursion_success_tendsto_one :
    Filter.Tendsto (fun k : ℕ => successWeight firstTwoTarget
      ((PiOverThree.searchRecursion 1 threeLevelState firstTwoTarget_isStarProjection k :
        ThreeLevelSpace →L[ℂ] ThreeLevelSpace) (threeLevelState : ThreeLevelSpace)))
      Filter.atTop (nhds 1) :=
  PiOverThree.searchRecursion_successWeight_tendsto_one
    1 threeLevelState firstTwoTarget_isStarProjection threeLevelState_initial_failure_lt_one

theorem threeLevelState_searchRecursion_complement_norm_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => ‖(1 - firstTwoTarget)
      ((PiOverThree.searchRecursion 1 threeLevelState firstTwoTarget_isStarProjection k :
        ThreeLevelSpace →L[ℂ] ThreeLevelSpace) (threeLevelState : ThreeLevelSpace))‖)
      Filter.atTop (nhds 0) :=
  PiOverThree.searchRecursion_complement_norm_tendsto_zero
    1 threeLevelState firstTwoTarget_isStarProjection threeLevelState_initial_failure_lt_one

theorem basisZero_searchRecursion_failure (k : ℕ) :
    failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 basisZero firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (basisZero : QubitSpace)) = 0 := by
  apply PiOverThree.searchRecursion_failureWeight_eq_zero
  change failureWeight firstBasisTarget (basisZero : QubitSpace) = 0
  simp [failureWeight, sub_apply]

theorem basisZero_searchRecursion_success (k : ℕ) :
    successWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 basisZero firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (basisZero : QubitSpace)) = 1 := by
  apply PiOverThree.searchRecursion_successWeight_eq_one
  change failureWeight firstBasisTarget (basisZero : QubitSpace) = 0
  simp [failureWeight, sub_apply]

theorem basisZero_searchRecursion_complement (k : ℕ) :
    (1 - firstBasisTarget)
      ((PiOverThree.searchRecursion 1 basisZero firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (basisZero : QubitSpace)) = 0 := by
  apply PiOverThree.searchRecursion_complement_eq_zero
  change failureWeight firstBasisTarget (basisZero : QubitSpace) = 0
  simp [failureWeight, sub_apply]

theorem basisOne_searchRecursion_failure (k : ℕ) :
    failureWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 basisOne firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (basisOne : QubitSpace)) = 1 := by
  apply PiOverThree.searchRecursion_failureWeight_eq_one
  change failureWeight firstBasisTarget (basisOne : QubitSpace) = 1
  simp [failureWeight, sub_apply, basisOne.normalized]

theorem basisOne_searchRecursion_success (k : ℕ) :
    successWeight firstBasisTarget
      ((PiOverThree.searchRecursion 1 basisOne firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (basisOne : QubitSpace)) = 0 := by
  apply PiOverThree.searchRecursion_successWeight_eq_zero
  change failureWeight firstBasisTarget (basisOne : QubitSpace) = 1
  simp [failureWeight, sub_apply, basisOne.normalized]

theorem basisOne_searchRecursion_target (k : ℕ) :
    firstBasisTarget
      ((PiOverThree.searchRecursion 1 basisOne firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (basisOne : QubitSpace)) = 0 := by
  apply PiOverThree.searchRecursion_target_eq_zero
  change failureWeight firstBasisTarget (basisOne : QubitSpace) = 1
  simp [failureWeight, sub_apply, basisOne.normalized]

end
end QFixLean.Examples
