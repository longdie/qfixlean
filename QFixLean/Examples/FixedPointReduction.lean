module

public import QFixLean.FixedPoint.PhaseSequence
public import QFixLean.FixedPoint.TwoDimensional
public import QFixLean.FixedPoint.Reduction
public import QFixLean.FixedPoint.PhaseBoundary
public import QFixLean.FixedPoint.PhaseConventions
public import QFixLean.Examples.Measurement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact checks of generalized phase execution and reduction

The physical qubit coordinates put the target first. The reduction uses the
opposite bad, good order. All values below are exact; these checks concern
general phase semantics, not the later Chebyshev choice of phase sequence.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

/-- Direct actual-operator calculation at the two π phases. -/
theorem rationalState_iterate_pi_direct :
    (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection Real.pi Real.pi :
      QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      WithLp.toLp 2 ![(-117 / 125 : ℂ), (44 / 125 : ℂ)] := by
  simp only [FixedPoint.coe_iterate, mul_apply_eq_comp, phaseRotation_pi]
  ext i
  fin_cases i <;>
    norm_num [sub_apply, firstBasisTarget_apply, PureState.projection_apply,
      rationalState, PiLp.inner_apply, Fin.sum_univ_two, map_ofNat]

/-- Both weights belong to the same directly computed output. -/
theorem rationalState_iterate_pi_weights :
    successWeight firstBasisTarget
      ((FixedPoint.iterate rationalState firstBasisTarget_isStarProjection Real.pi Real.pi :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (117 / 125 : ℝ) ^ 2 ∧
    failureWeight firstBasisTarget
      ((FixedPoint.iterate rationalState firstBasisTarget_isStarProjection Real.pi Real.pi :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) = (44 / 125 : ℝ) ^ 2 := by
  rw [rationalState_iterate_pi_direct]
  norm_num [successWeight, failureWeight, firstBasisTarget_apply, sub_apply,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-- Listing target then source phases means that the target actually acts first. -/
theorem rationalState_split_phase_order :
    FixedPoint.execute rationalState firstBasisTarget_isStarProjection
      [(Real.pi, 0), (0, Real.pi)] =
    FixedPoint.iterate rationalState firstBasisTarget_isStarProjection Real.pi Real.pi := by
  apply Subtype.ext
  simp [FixedPoint.coe_iterate]

/-- Reversing the time order has a different exact physical output. -/
theorem rationalState_reverse_phase_order :
    (FixedPoint.execute rationalState firstBasisTarget_isStarProjection
      [(0, Real.pi), (Real.pi, 0)] : QubitSpace →L[ℂ] QubitSpace)
      (rationalState : QubitSpace) =
      WithLp.toLp 2 ![(3 / 5 : ℂ), (-4 / 5 : ℂ)] := by
  rw [FixedPoint.execute_pair]
  change (phaseRotation rationalState.projection 0 * phaseRotation firstBasisTarget Real.pi)
    ((phaseRotation rationalState.projection Real.pi * phaseRotation firstBasisTarget 0)
      (rationalState : QubitSpace)) = _
  simp only [phaseRotation_zero, one_mul, mul_one,
    PureState.phaseRotation_projection_self, phaseFactor_pi]
  rw [map_smul, phaseRotation_pi]
  ext i
  fin_cases i <;> norm_num [sub_apply, firstBasisTarget_apply, rationalState]

/-- The two lists cannot be interchanged even though they use the same phases. -/
theorem rationalState_phase_order_matters :
    (FixedPoint.execute rationalState firstBasisTarget_isStarProjection
      [(Real.pi, 0), (0, Real.pi)] : QubitSpace →L[ℂ] QubitSpace)
      (rationalState : QubitSpace) ≠
    (FixedPoint.execute rationalState firstBasisTarget_isStarProjection
      [(0, Real.pi), (Real.pi, 0)] : QubitSpace →L[ℂ] QubitSpace)
      (rationalState : QubitSpace) := by
  rw [rationalState_split_phase_order, rationalState_iterate_pi_direct,
    rationalState_reverse_phase_order]
  intro h
  have h0 := congrArg (fun v : QubitSpace => v 0) h
  norm_num at h0

/-- A nonreal phase distinguishes positive target angles from their conjugates. -/
theorem rationalState_target_half_pi :
    (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
      (Real.pi / 2) 0 : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      WithLp.toLp 2 ![(3 / 5 : ℂ) * Complex.I, (4 / 5 : ℂ)] := by
  have hp : phaseFactor (Real.pi / 2) = Complex.I := by
    rw [phaseFactor, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  simp only [FixedPoint.coe_iterate, phaseRotation_zero, one_mul]
  rw [phaseRotation_apply_components, hp]
  ext i
  fin_cases i <;> norm_num [sub_apply, firstBasisTarget_apply, rationalState, mul_comm]

/-- Positive source phase uses +i on the fixed reference state itself. -/
theorem rationalState_source_half_pi :
    (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
      0 (Real.pi / 2) : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      Complex.I • (rationalState : QubitSpace) := by
  have hp : phaseFactor (Real.pi / 2) = Complex.I := by
    rw [phaseFactor, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  simp only [FixedPoint.coe_iterate, phaseRotation_zero, mul_one,
    PureState.phaseRotation_projection_self, hp]

/-- P14's negative source angle and the iterate's outer minus are both retained. -/
theorem rationalState_p14_source_half_pi :
    (FixedPoint.p14Iterate rationalState firstBasisTarget_isStarProjection
      (Real.pi / 2) 0 : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      Complex.I • (rationalState : QubitSpace) := by
  have hp : phaseFactor (Real.pi / 2) = Complex.I := by
    rw [phaseFactor, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  simp [FixedPoint.coe_p14Iterate, PureState.phaseRotation_projection_self,
    phaseFactor_neg, hp]

/-- Independent matrix calculation in bad, good order, before using any
Hilbert-space bridge to compare it with the direct physical calculation. -/
theorem rationalState_iterate_pi_coordinates :
    FixedPoint.TwoDimensional.applyMatrix
      (FixedPoint.TwoDimensional.iterateMatrix (4 / 5) (3 / 5) Real.pi Real.pi)
      (FixedPoint.TwoDimensional.initial (4 / 5) (3 / 5)) =
      WithLp.toLp 2 ![(44 / 125 : ℂ), (-117 / 125 : ℂ)] := by
  ext i
  fin_cases i <;>
    norm_num [FixedPoint.TwoDimensional.applyMatrix_apply,
      FixedPoint.TwoDimensional.iterateMatrix_entries]

/-- The physical target is first, while the reduction orders bad before good. -/
theorem rationalState_reduction_amplitudes :
    FixedPoint.Reduction.failureAmplitude rationalState firstBasisTarget = (4 / 5 : ℝ) ∧
    FixedPoint.Reduction.successAmplitude rationalState firstBasisTarget = (3 / 5 : ℝ) := by
  constructor
  · rw [FixedPoint.Reduction.failureAmplitude, rationalState_success]
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  · rw [FixedPoint.Reduction.successAmplitude, rationalState_success]
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num

theorem rationalState_bad_direction :
    FixedPoint.Reduction.badDirection rationalState firstBasisTarget = (basisOne : QubitSpace) := by
  rw [FixedPoint.Reduction.badDirection, rationalState_reduction_amplitudes.1]
  ext i
  fin_cases i <;> norm_num [sub_apply, firstBasisTarget_apply, rationalState, basisOne]

theorem rationalState_good_direction :
    FixedPoint.Reduction.goodDirection rationalState firstBasisTarget = (basisZero : QubitSpace) := by
  rw [FixedPoint.Reduction.goodDirection, rationalState_reduction_amplitudes.2]
  ext i
  fin_cases i <;> norm_num [firstBasisTarget_apply, rationalState, basisZero]

/-- Synthesis explicitly swaps the bad, good coordinates to physical order. -/
theorem rationalState_embed_coordinates (v : FixedPoint.TwoDimensional.Coord) :
    FixedPoint.Reduction.embed rationalState firstBasisTarget v =
      WithLp.toLp 2 ![v 1, v 0] := by
  rw [FixedPoint.Reduction.embed_apply, rationalState_bad_direction, rationalState_good_direction]
  ext i
  fin_cases i <;> simp [basisOne, basisZero]

/-- A second proof of the actual output, using the general intertwining theorem
and independently calculated matrix coordinates rather than direct expansion. -/
theorem rationalState_iterate_pi_via_reduction :
    (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection Real.pi Real.pi :
      QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      WithLp.toLp 2 ![(-117 / 125 : ℂ), (44 / 125 : ℂ)] := by
  have h0 : 0 < successWeight firstBasisTarget (rationalState : QubitSpace) := by
    rw [rationalState_success]
    norm_num
  have h1 : successWeight firstBasisTarget (rationalState : QubitSpace) < 1 := by
    rw [rationalState_success]
    norm_num
  have h := FixedPoint.Reduction.iterate_embed rationalState firstBasisTarget_isStarProjection
    h0 h1 Real.pi Real.pi
    (FixedPoint.TwoDimensional.initial
      (FixedPoint.Reduction.failureAmplitude rationalState firstBasisTarget)
      (FixedPoint.Reduction.successAmplitude rationalState firstBasisTarget))
  rw [FixedPoint.Reduction.embed_initial rationalState h0 h1,
    rationalState_reduction_amplitudes.1, rationalState_reduction_amplitudes.2,
    rationalState_iterate_pi_coordinates, rationalState_embed_coordinates] at h
  exact h

/-- A rank-two ambient target uses exactly the same actual-output bridge. -/
theorem threeLevel_fixedPoint_output_coordinates (ps : List (ℝ × ℝ)) :
    (FixedPoint.output threeLevelState firstTwoTarget_isStarProjection ps : ThreeLevelSpace) =
      FixedPoint.Reduction.embed threeLevelState firstTwoTarget
        (FixedPoint.Reduction.outputCoordinates threeLevelState firstTwoTarget ps) ∧
    successWeight firstTwoTarget
      (FixedPoint.output threeLevelState firstTwoTarget_isStarProjection ps : ThreeLevelSpace) =
      ‖FixedPoint.Reduction.outputCoordinates threeLevelState firstTwoTarget ps 1‖ ^ 2 ∧
    failureWeight firstTwoTarget
      (FixedPoint.output threeLevelState firstTwoTarget_isStarProjection ps : ThreeLevelSpace) =
      ‖FixedPoint.Reduction.outputCoordinates threeLevelState firstTwoTarget ps 0‖ ^ 2 := by
  have h0 : 0 < successWeight firstTwoTarget (threeLevelState : ThreeLevelSpace) := by
    rw [threeLevelState_success]
    norm_num
  have h1 : successWeight firstTwoTarget (threeLevelState : ThreeLevelSpace) < 1 := by
    rw [threeLevelState_success]
    norm_num
  exact ⟨FixedPoint.Reduction.output_eq_embed threeLevelState firstTwoTarget_isStarProjection
      h0 h1 ps,
    FixedPoint.Reduction.output_successWeight threeLevelState firstTwoTarget_isStarProjection
      h0 h1 ps,
    FixedPoint.Reduction.output_failureWeight threeLevelState firstTwoTarget_isStarProjection
      h0 h1 ps⟩

theorem threeLevel_fixedPoint_output_in_searchSpace (ps : List (ℝ × ℝ)) :
    (FixedPoint.output threeLevelState firstTwoTarget_isStarProjection ps : ThreeLevelSpace) ∈
      FixedPoint.searchSpace threeLevelState firstTwoTarget :=
  FixedPoint.output_mem_searchSpace threeLevelState firstTwoTarget_isStarProjection ps

/-- The completely bad basis input needs no normalized good direction. -/
theorem basisOne_fixedPoint_probabilities (ps : List (ℝ × ℝ)) :
    successWeight firstBasisTarget
      ((FixedPoint.execute basisOne firstBasisTarget_isStarProjection ps :
        QubitSpace →L[ℂ] QubitSpace) (basisOne : QubitSpace)) = 0 ∧
    failureWeight firstBasisTarget
      ((FixedPoint.execute basisOne firstBasisTarget_isStarProjection ps :
        QubitSpace →L[ℂ] QubitSpace) (basisOne : QubitSpace)) = 1 := by
  apply FixedPoint.execute_probabilities_of_success_zero basisOne
    firstBasisTarget_isStarProjection
  simp [successWeight]

/-- The completely good basis input needs no normalized bad direction. -/
theorem basisZero_fixedPoint_probabilities (ps : List (ℝ × ℝ)) :
    successWeight firstBasisTarget
      ((FixedPoint.execute basisZero firstBasisTarget_isStarProjection ps :
        QubitSpace →L[ℂ] QubitSpace) (basisZero : QubitSpace)) = 1 ∧
    failureWeight firstBasisTarget
      ((FixedPoint.execute basisZero firstBasisTarget_isStarProjection ps :
        QubitSpace →L[ℂ] QubitSpace) (basisZero : QubitSpace)) = 0 := by
  apply FixedPoint.execute_probabilities_of_success_one basisZero
    firstBasisTarget_isStarProjection
  simp [successWeight]

end
end QFixLean.Examples
