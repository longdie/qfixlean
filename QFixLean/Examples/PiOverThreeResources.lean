module

public import QFixLean.PiOverThree.Resources
public import QFixLean.Examples.PiOverThreeConvergence
import Mathlib.Tactic.NormNum

/-!
# A complete exact π/3 search example with resources

The interpreted construction prepares each output from the fixed rational
source `(3/5, 4/5)`. Its unoptimized syntax counts target-phase queries,
base `U`/`U†` calls and source-phase calls separately. Even for identity `U`,
the base-call count records syntactic primitive occurrences; it is not a
claim that an optimized implementation must execute identity gates.

The probability and limit facts from earlier modules are transported through
the proved operator semantics of this same counted construction. A
three-dimensional target retaining two coordinates illustrates the same joint
semantic, probability and resource interface without a rank-one restriction.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

open PiOverThree

/-- The actual output of the counted construction on the original fixed source. -/
def rationalState_searchConstructionOutput (k : ℕ) : QubitSpace :=
  (Construction.interpret 1 rationalState firstBasisTarget_isStarProjection
    (searchConstruction k) : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)

@[simp]
theorem rationalState_searchConstructionOutput_eq (k : ℕ) :
    rationalState_searchConstructionOutput k =
      (searchRecursion 1 rationalState firstBasisTarget_isStarProjection k :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) := by
  simp only [rationalState_searchConstructionOutput, interpret_searchConstruction]

theorem rationalState_searchConstruction_normalized (k : ℕ) :
    ‖rationalState_searchConstructionOutput k‖ = 1 := by
  rw [rationalState_searchConstructionOutput_eq]
  exact searchRecursion_normalized 1 rationalState firstBasisTarget_isStarProjection k

theorem rationalState_searchConstruction_failure (k : ℕ) :
    failureWeight firstBasisTarget (rationalState_searchConstructionOutput k) =
      (16 / 25 : ℝ) ^ (2 * (searchConstruction k).targetQueries + 1) := by
  unfold rationalState_searchConstructionOutput
  rw [searchConstruction_failureWeight]
  change failureWeight firstBasisTarget (rationalState : QubitSpace) ^ _ = _
  rw [rationalState_failure]

theorem rationalState_searchConstruction_success (k : ℕ) :
    successWeight firstBasisTarget (rationalState_searchConstructionOutput k) =
      1 - (16 / 25 : ℝ) ^ (2 * (searchConstruction k).targetQueries + 1) := by
  unfold rationalState_searchConstructionOutput
  rw [searchConstruction_successWeight]
  change 1 - failureWeight firstBasisTarget (rationalState : QubitSpace) ^ _ = _
  rw [rationalState_failure]

/-- One statement ties the counted construction to its actual normalized output
and both exact probabilities. Counts are not inferred from the identity semantics. -/
theorem rationalState_searchConstruction_summary (k : ℕ) :
    ‖rationalState_searchConstructionOutput k‖ = 1 ∧
    (searchConstruction k).targetQueries = ((3 : ℕ) ^ k - 1) / 2 ∧
    (searchConstruction k).baseCalls = (3 : ℕ) ^ k ∧
    (searchConstruction k).sourceCalls = (searchConstruction k).targetQueries ∧
    failureWeight firstBasisTarget (rationalState_searchConstructionOutput k) =
      (16 / 25 : ℝ) ^ (2 * (searchConstruction k).targetQueries + 1) ∧
    successWeight firstBasisTarget (rationalState_searchConstructionOutput k) =
      1 - (16 / 25 : ℝ) ^ (2 * (searchConstruction k).targetQueries + 1) :=
  ⟨rationalState_searchConstruction_normalized k, searchConstruction_targetQueries k,
    searchConstruction_baseCalls k, searchConstruction_sourceCalls k,
    rationalState_searchConstruction_failure k, rationalState_searchConstruction_success k⟩

/-- Direct reduction of the signed syntax, independent of the general closed forms. -/
theorem searchConstruction_first_three_counts :
    ((searchConstruction 0).targetQueries, (searchConstruction 0).baseCalls,
      (searchConstruction 0).sourceCalls) = (0, 1, 0) ∧
    ((searchConstruction 1).targetQueries, (searchConstruction 1).baseCalls,
      (searchConstruction 1).sourceCalls) = (1, 3, 1) ∧
    ((searchConstruction 2).targetQueries, (searchConstruction 2).baseCalls,
      (searchConstruction 2).sourceCalls) = (4, 9, 4) := by
  decide

theorem rationalState_searchConstruction_zero :
    failureWeight firstBasisTarget (rationalState_searchConstructionOutput 0) = (16 / 25 : ℝ) ∧
    successWeight firstBasisTarget (rationalState_searchConstructionOutput 0) =
      1 - (16 / 25 : ℝ) ∧
    ((searchConstruction 0).targetQueries, (searchConstruction 0).baseCalls,
      (searchConstruction 0).sourceCalls) = (0, 1, 0) := by
  constructor
  · rw [rationalState_searchConstructionOutput_eq]
    exact rationalState_searchRecursion_zero_failure
  constructor
  · rw [rationalState_searchConstructionOutput_eq, rationalState_searchRecursion_success]
    norm_num
  · exact searchConstruction_first_three_counts.1

/-- Level one agrees with the independently checked M07 value `4096/15625`. -/
theorem rationalState_searchConstruction_one :
    failureWeight firstBasisTarget (rationalState_searchConstructionOutput 1) =
      (4096 / 15625 : ℝ) ∧
    successWeight firstBasisTarget (rationalState_searchConstructionOutput 1) =
      1 - (16 / 25 : ℝ) ^ 3 ∧
    ((searchConstruction 1).targetQueries, (searchConstruction 1).baseCalls,
      (searchConstruction 1).sourceCalls) = (1, 3, 1) := by
  constructor
  · rw [rationalState_searchConstructionOutput_eq]
    exact rationalState_searchRecursion_one_failure
  constructor
  · rw [rationalState_searchConstructionOutput_eq, rationalState_searchRecursion_success]
    norm_num
  · exact searchConstruction_first_three_counts.2.1

theorem rationalState_searchConstruction_two :
    failureWeight firstBasisTarget (rationalState_searchConstructionOutput 2) =
      (16 / 25 : ℝ) ^ 9 ∧
    successWeight firstBasisTarget (rationalState_searchConstructionOutput 2) =
      1 - (16 / 25 : ℝ) ^ 9 ∧
    ((searchConstruction 2).targetQueries, (searchConstruction 2).baseCalls,
      (searchConstruction 2).sourceCalls) = (4, 9, 4) := by
  constructor
  · rw [rationalState_searchConstructionOutput_eq]
    exact rationalState_searchRecursion_two_failure
  constructor
  · rw [rationalState_searchConstructionOutput_eq, rationalState_searchRecursion_success]
    norm_num
  · exact searchConstruction_first_three_counts.2.2

theorem rationalState_searchConstruction_failure_antitone :
    Antitone (fun k : ℕ =>
      failureWeight firstBasisTarget (rationalState_searchConstructionOutput k)) := by
  simpa only [rationalState_searchConstructionOutput_eq] using
    searchRecursion_failureWeight_antitone 1 rationalState firstBasisTarget_isStarProjection

theorem rationalState_searchConstruction_success_monotone :
    Monotone (fun k : ℕ =>
      successWeight firstBasisTarget (rationalState_searchConstructionOutput k)) := by
  simpa only [rationalState_searchConstructionOutput_eq] using
    searchRecursion_successWeight_monotone 1 rationalState firstBasisTarget_isStarProjection

theorem rationalState_searchConstruction_failure_tendsto_zero :
    Filter.Tendsto (fun k : ℕ =>
      failureWeight firstBasisTarget (rationalState_searchConstructionOutput k))
      Filter.atTop (nhds 0) := by
  simpa only [rationalState_searchConstructionOutput_eq] using
    rationalState_searchRecursion_failure_tendsto_zero

theorem rationalState_searchConstruction_success_tendsto_one :
    Filter.Tendsto (fun k : ℕ =>
      successWeight firstBasisTarget (rationalState_searchConstructionOutput k))
      Filter.atTop (nhds 1) := by
  simpa only [rationalState_searchConstructionOutput_eq] using
    rationalState_searchRecursion_success_tendsto_one

theorem rationalState_searchConstruction_complement_norm_tendsto_zero :
    Filter.Tendsto (fun k : ℕ =>
      ‖(1 - firstBasisTarget) (rationalState_searchConstructionOutput k)‖)
      Filter.atTop (nhds 0) := by
  simpa only [rationalState_searchConstructionOutput_eq] using
    rationalState_searchRecursion_complement_norm_tendsto_zero

/-- The same construction works with a three-dimensional, rank-two target;
its semantics, structural counts and actual failure probability are checked together. -/
theorem threeLevelState_searchConstruction_summary (k : ℕ) :
    Construction.interpret 1 threeLevelState firstTwoTarget_isStarProjection
      (searchConstruction k) =
      searchRecursion 1 threeLevelState firstTwoTarget_isStarProjection k ∧
    (searchConstruction k).targetQueries = ((3 : ℕ) ^ k - 1) / 2 ∧
    (searchConstruction k).baseCalls = (3 : ℕ) ^ k ∧
    (searchConstruction k).sourceCalls = (searchConstruction k).targetQueries ∧
    failureWeight firstTwoTarget
      ((Construction.interpret 1 threeLevelState firstTwoTarget_isStarProjection
        (searchConstruction k) : ThreeLevelSpace →L[ℂ] ThreeLevelSpace)
        (threeLevelState : ThreeLevelSpace)) = (4 / 9 : ℝ) ^ ((3 : ℕ) ^ k) := by
  refine ⟨interpret_searchConstruction _ _ _ _, searchConstruction_targetQueries k,
    searchConstruction_baseCalls k, searchConstruction_sourceCalls k, ?_⟩
  rw [interpret_searchConstruction]
  exact threeLevelState_searchRecursion_failure k

end
end QFixLean.Examples
