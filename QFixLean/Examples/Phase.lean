module

public import QFixLean.Basic.PhaseRotation
public import QFixLean.Examples.Measurement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact selective phase examples

The first basis target changes only the first qubit amplitude. The examples
retain the exact complex phase, while measurement against that same target
keeps probabilities `9/25` and `16/25`. A three-dimensional example phases two
coordinates at once.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

theorem firstBasisTarget_phaseRotation_apply (φ : ℝ) (v : QubitSpace) :
    phaseRotation firstBasisTarget φ v = WithLp.toLp 2 ![phaseFactor φ * v 0, v 1] := by
  change selectivePhase firstBasisTarget (phaseFactor φ) v = _
  ext i
  fin_cases i
  · simp [selectivePhase_apply, firstBasisTarget_apply]
    ring
  · simp [selectivePhase_apply, firstBasisTarget_apply]

theorem rationalState_phaseRotation (φ : ℝ) :
    phaseRotation firstBasisTarget φ (rationalState : QubitSpace) =
      WithLp.toLp 2 ![phaseFactor φ * (3 / 5), 4 / 5] := by
  rw [firstBasisTarget_phaseRotation_apply]
  rfl

theorem rationalState_phaseRotation_pi :
    phaseRotation firstBasisTarget Real.pi (rationalState : QubitSpace) =
      WithLp.toLp 2 ![-3 / 5, 4 / 5] := by
  rw [rationalState_phaseRotation, phaseFactor_pi]
  norm_num

theorem rationalState_phaseRotation_pi_div_three :
    phaseRotation firstBasisTarget (Real.pi / 3) (rationalState : QubitSpace) =
      WithLp.toLp 2 ![((1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 / 2 : ℝ) : ℂ)) *
        (3 / 5), 4 / 5] := by
  rw [rationalState_phaseRotation, phaseFactor_pi_div_three]

/-- The bundled pure-state action has precisely the same underlying vector. -/
theorem rationalState_phaseRotation_map (φ : ℝ) :
    (PureState.map (phaseRotationUnitary firstBasisTarget_isStarProjection φ)
      rationalState : QubitSpace) = WithLp.toLp 2 ![phaseFactor φ * (3 / 5), 4 / 5] := by
  change phaseRotation firstBasisTarget φ (rationalState : QubitSpace) = _
  exact rationalState_phaseRotation φ

theorem rationalState_phaseRotation_success (φ : ℝ) :
    successWeight firstBasisTarget
      (phaseRotation firstBasisTarget φ (rationalState : QubitSpace)) = (9 / 25 : ℝ) := by
  rw [successWeight_phaseRotation firstBasisTarget_isStarProjection, rationalState_success]

theorem rationalState_phaseRotation_failure (φ : ℝ) :
    failureWeight firstBasisTarget
      (phaseRotation firstBasisTarget φ (rationalState : QubitSpace)) = (16 / 25 : ℝ) := by
  rw [failureWeight_phaseRotation firstBasisTarget_isStarProjection, rationalState_failure]

theorem firstTwoTarget_phaseRotation_apply (φ : ℝ) (v : ThreeLevelSpace) :
    phaseRotation firstTwoTarget φ v =
      WithLp.toLp 2 ![phaseFactor φ * v 0, phaseFactor φ * v 1, v 2] := by
  change selectivePhase firstTwoTarget (phaseFactor φ) v = _
  ext i
  fin_cases i <;> simp [selectivePhase_apply, firstTwoTarget_apply] <;> ring

end
end QFixLean.Examples
