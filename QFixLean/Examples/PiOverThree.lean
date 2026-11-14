module

public import QFixLean.PiOverThree.Step
public import QFixLean.Basic.PhaseFactor
public import QFixLean.Examples.Measurement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Exact π/3 search-step examples

For the normalized state `(3/5, 4/5)`, identity preparation and the first-basis
target, the failure probability changes from `16/25` to `(16/25)^3`.
The direct vector calculation unfolds the actual operator product and its
coordinates, independently of the general failure-vector and cubing theorems.
Its result is then compared with the general theorem at the same exact input.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

/-- Direct coordinate expansion of the actual search product. This proof does
not use the general step expansion, failure-vector or error-cubing theorem. -/
theorem rationalState_step_failure_direct :
    (1 - firstBasisTarget)
      (PiOverThree.step (1 : QubitSpace →L[ℂ] QubitSpace) firstBasisTarget
        (rationalState : QubitSpace) (phaseFactor (Real.pi / 3)) (rationalState : QubitSpace)) =
      WithLp.toLp 2 ![0, phaseFactor (Real.pi / 3) * (64 / 125)] := by
  have hz := phaseFactor_pi_div_three_sub_one_sq
  ext i
  fin_cases i
  · simp [PiOverThree.step, selectivePhase_apply, InnerProductSpace.rankOne_apply,
      firstBasisTarget_apply, rationalState, PiLp.inner_apply, Fin.sum_univ_two, map_ofNat]
  · simp [PiOverThree.step, selectivePhase_apply, InnerProductSpace.rankOne_apply,
      firstBasisTarget_apply, rationalState, PiLp.inner_apply, Fin.sum_univ_two, map_ofNat]
    linear_combination (36 / 125 : ℂ) * hz

/-- The general failure-vector theorem yields the same exact vector as the
independent coordinate expansion above. -/
theorem rationalState_searchStep_failure_vector :
    (1 - firstBasisTarget)
      ((PiOverThree.searchStep 1 rationalState firstBasisTarget_isStarProjection :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      WithLp.toLp 2 ![0, phaseFactor (Real.pi / 3) * (64 / 125)] := by
  rw [PiOverThree.searchStep_failure_vector]
  change (phaseFactor (Real.pi / 3) *
      (failureWeight firstBasisTarget (rationalState : QubitSpace) : ℂ)) •
      (1 - firstBasisTarget) (rationalState : QubitSpace) = _
  rw [rationalState_failure]
  ext i
  fin_cases i <;> norm_num [sub_apply, firstBasisTarget_apply, rationalState, mul_assoc]

/-- A direct squared-norm calculation after expanding the actual product. -/
theorem rationalState_searchStep_failure :
    failureWeight firstBasisTarget
      ((PiOverThree.searchStep 1 rationalState firstBasisTarget_isStarProjection :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (4096 / 15625 : ℝ) := by
  unfold failureWeight
  rw [PiOverThree.coe_searchStep]
  change ‖(1 - firstBasisTarget)
      (PiOverThree.step (1 : QubitSpace →L[ℂ] QubitSpace) firstBasisTarget
        (rationalState : QubitSpace) (phaseFactor (Real.pi / 3)) (rationalState : QubitSpace))‖ ^ 2 = _
  rw [rationalState_step_failure_direct]
  norm_num [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, norm_mul]

/-- The general error-cubing theorem agrees with the independent calculation. -/
theorem rationalState_searchStep_failure_cubed :
    failureWeight firstBasisTarget
      ((PiOverThree.searchStep 1 rationalState firstBasisTarget_isStarProjection :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (16 / 25 : ℝ) ^ 3 := by
  rw [PiOverThree.searchStep_failureWeight]
  change (failureWeight firstBasisTarget (rationalState : QubitSpace)) ^ 3 = _
  rw [rationalState_failure]

theorem rationalState_searchStep_success :
    successWeight firstBasisTarget
      ((PiOverThree.searchStep 1 rationalState firstBasisTarget_isStarProjection :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (11529 / 15625 : ℝ) := by
  rw [PiOverThree.searchStep_successWeight]
  change 1 - (failureWeight firstBasisTarget (rationalState : QubitSpace)) ^ 3 = _
  rw [rationalState_failure]
  norm_num

end
end QFixLean.Examples
