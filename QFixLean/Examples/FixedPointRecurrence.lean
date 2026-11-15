module

public import QFixLean.Examples.FixedPointReduction
public import QFixLean.FixedPoint.AmplitudeRecurrence
import Mathlib.Tactic.Ring

/-!
# Exact checks of the actual-output amplitude recurrence

Physical qubit coordinates are target, bad; canonical coordinates are bad,
good. The examples retain the global phase before comparing probabilities.
The nonreal example is computed directly from the actual selective phases,
independently of the recurrence calculation.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

private theorem phaseFactor_half_pi : phaseFactor (Real.pi / 2) = Complex.I := by
  rw [phaseFactor, mul_comm Complex.I, Complex.exp_mul_I]
  simp

/-- Direct computation of a genuinely complex output using actual operators. -/
theorem rationalState_nonreal_iterate_direct :
    (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
      Real.pi (Real.pi / 2) : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      WithLp.toLp 2 ![((-96 + 21 * Complex.I) / 125 : ℂ),
        ((72 + 28 * Complex.I) / 125 : ℂ)] := by
  simp only [FixedPoint.coe_iterate, mul_apply_eq_comp]
  rw [phaseRotation_pi, phaseRotation, selectivePhase_apply, phaseFactor_half_pi]
  ext i
  fin_cases i <;>
    norm_num [sub_apply, firstBasisTarget_apply, PureState.projection_apply,
      rationalState, PiLp.inner_apply, Fin.sum_univ_two, map_ofNat] <;> ring

/-- The actual nonreal vector's weights, before any recurrence bridge is used. -/
theorem rationalState_nonreal_iterate_weights_direct :
    successWeight firstBasisTarget
      ((FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
        Real.pi (Real.pi / 2) : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      (9657 / 15625 : ℝ) ∧
    failureWeight firstBasisTarget
      ((FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
        Real.pi (Real.pi / 2) : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      (5968 / 15625 : ℝ) := by
  rw [rationalState_nonreal_iterate_direct]
  norm_num [successWeight, failureWeight, firstBasisTarget_apply, sub_apply,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]

open FixedPoint.AmplitudeRecurrence

/-- Empty execution still has amplitude index one, not zero. -/
theorem phaseRecurrence_empty (x : ℂ) :
    PhaseRecurrence.value x (angles []) = x ∧ finalCoupled x [] = (x, 1) := by
  simp [finalCoupled, coupledRun, rawAngles]

/-- Empty execution preserves any prepared input; the terminal index is one. -/
theorem phaseRecurrence_empty_output {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ψ₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    (FixedPoint.output ψ₀ hP [] : E) = (ψ₀ : E) ∧
    outputAmplitude ψ₀ P [] = (FixedPoint.Reduction.failureAmplitude ψ₀ P : ℂ) :=
  ⟨rfl, rfl⟩

/-- At zero actual steps the output remains the prepared state and a₁=x. -/
theorem rationalState_empty_recurrence :
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection [] : QubitSpace) =
      (rationalState : QubitSpace) ∧
    outputAmplitude rationalState firstBasisTarget [] = (4 / 5 : ℂ) ∧
    failureWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection [] : QubitSpace) =
      (16 / 25 : ℝ) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [outputAmplitude, rationalState_reduction_amplitudes.1]
  · exact rationalState_failure

/-- The π/π singleton uses recurrence angles zero and exactly two π. -/
theorem phaseRecurrence_pi_angles :
    angles [(Real.pi, Real.pi)] = [0, 2 * Real.pi] := by
  simp
  ring

/-- Exact raw and recurrence angle order for a single actual iterate. -/
theorem phaseRecurrence_singleton_angles (α β : ℝ) :
    0 :: rawAngles [(α, β)] = [0, -α, β] ∧
    angles [(α, β)] = [Real.pi - α, β + Real.pi] := by simp

/-- Two actual iterations use four recurrence angles and finish at index five. -/
theorem phaseRecurrence_pair_angles (α₁ β₁ α₂ β₂ : ℝ) :
    0 :: rawAngles [(α₁, β₁), (α₂, β₂)] = [0, -α₁, β₁, -α₂, β₂] ∧
    angles [(α₁, β₁), (α₂, β₂)] =
      [Real.pi - α₁, β₁ + Real.pi, Real.pi - α₂, β₂ + Real.pi] ∧
    (angles [(α₁, β₁), (α₂, β₂)]).length + 1 = 5 := by simp

/-- Direct recurrence expansion gives the cubic for the two π phases. -/
theorem phaseRecurrence_pi_cubic (x : ℂ) :
    PhaseRecurrence.value x (angles [(Real.pi, Real.pi)]) = 4 * x ^ 3 - 3 * x := by
  simp [PhaseRecurrence.value, PhaseRecurrence.state, PhaseRecurrence.step,
    PhaseRecurrence.coefficient, phaseFactor_add, phaseFactor_neg]
  ring

/-- Two split physical phases use index five but yield the same cubic here. -/
theorem phaseRecurrence_split_cubic (x : ℂ) :
    PhaseRecurrence.value x (angles [(Real.pi, 0), (0, Real.pi)]) =
      4 * x ^ 3 - 3 * x := by
  simp [PhaseRecurrence.value, PhaseRecurrence.state, PhaseRecurrence.step,
    PhaseRecurrence.coefficient, phaseFactor_add, phaseFactor_neg]
  ring

/-- Reversing the same steps changes their recurrence to the initial amplitude. -/
theorem phaseRecurrence_reverse_linear (x : ℂ) :
    PhaseRecurrence.value x (angles [(0, Real.pi), (Real.pi, 0)]) = x := by
  simp [PhaseRecurrence.value, PhaseRecurrence.state, PhaseRecurrence.step,
    PhaseRecurrence.coefficient, phaseFactor_add, phaseFactor_neg]
  ring

/-- The terminal polynomial is evaluated through the proved scalar interface. -/
theorem rationalState_pi_polynomial_eval :
    (outputPolynomial [(Real.pi, Real.pi)]).eval (4 / 5 : ℂ) = -44 / 125 := by
  rw [outputPolynomial, PhaseRecurrence.polynomial_eval, phaseRecurrence_pi_cubic]
  norm_num

/-- The complex example has a genuinely nonreal recurrence term. -/
theorem rationalState_nonreal_recurrence :
    PhaseRecurrence.value (4 / 5 : ℂ) (angles [(Real.pi, Real.pi / 2)]) =
      (28 - 72 * Complex.I) / 125 := by
  simp [PhaseRecurrence.value, PhaseRecurrence.state, PhaseRecurrence.step,
    PhaseRecurrence.coefficient, phaseFactor_add, phaseFactor_neg,
    phaseFactor_half_pi]
  ring

private theorem rationalState_success_pos :
    0 < successWeight firstBasisTarget (rationalState : QubitSpace) := by
  rw [rationalState_success]
  norm_num

private theorem rationalState_success_lt_one :
    successWeight firstBasisTarget (rationalState : QubitSpace) < 1 := by
  rw [rationalState_success]
  norm_num

/-- The same actual physical bad coordinate is obtained from the recurrence,
with the complete source phase retained. -/
theorem rationalState_physical_bad_recurrence (ps : List (ℝ × ℝ)) :
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection ps : QubitSpace) 1 =
      FixedPoint.badPhase ps * PhaseRecurrence.value (4 / 5 : ℂ) (angles ps) := by
  rw [FixedPoint.Reduction.output_eq_embed rationalState firstBasisTarget_isStarProjection
    rationalState_success_pos rationalState_success_lt_one, rationalState_embed_coordinates]
  change FixedPoint.Reduction.outputCoordinates rationalState firstBasisTarget ps 0 = _
  rw [outputCoordinates_bad rationalState firstBasisTarget_isStarProjection,
    outputAmplitude, rationalState_reduction_amplitudes.1]
  norm_num

/-- The recurrence term is negative, and the source phase changes its sign. -/
theorem rationalState_pi_recurrence_signed :
    PhaseRecurrence.value (4 / 5 : ℂ) (angles [(Real.pi, Real.pi)]) = -44 / 125 ∧
    FixedPoint.badPhase [(Real.pi, Real.pi)] = -1 ∧
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection
      [(Real.pi, Real.pi)] : QubitSpace) 1 = 44 / 125 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phaseRecurrence_pi_cubic]
    norm_num
  · simp [FixedPoint.badPhase]
  · rw [rationalState_physical_bad_recurrence, phaseRecurrence_pi_cubic]
    norm_num [FixedPoint.badPhase]

/-- The general recurrence theorem recovers both exact π/π probabilities. -/
theorem rationalState_pi_recurrence_weights :
    failureWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection
        [(Real.pi, Real.pi)] : QubitSpace) = (44 / 125 : ℝ) ^ 2 ∧
    successWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection
        [(Real.pi, Real.pi)] : QubitSpace) = (117 / 125 : ℝ) ^ 2 := by
  rw [output_failureWeight rationalState firstBasisTarget_isStarProjection,
    output_successWeight rationalState firstBasisTarget_isStarProjection,
    outputAmplitude, rationalState_reduction_amplitudes.1]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [phaseRecurrence_pi_cubic]
  norm_num

/-- Independent actual-operator and recurrence paths agree for both time orders. -/
theorem rationalState_split_reverse_recurrence :
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection
      [(Real.pi, 0), (0, Real.pi)] : QubitSpace) 1 = 44 / 125 ∧
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection
      [(0, Real.pi), (Real.pi, 0)] : QubitSpace) 1 = -4 / 5 ∧
    (FixedPoint.execute rationalState firstBasisTarget_isStarProjection
      [(Real.pi, 0), (0, Real.pi)] : QubitSpace →L[ℂ] QubitSpace)
      (rationalState : QubitSpace) = WithLp.toLp 2 ![(-117 / 125 : ℂ), (44 / 125 : ℂ)] ∧
    (FixedPoint.execute rationalState firstBasisTarget_isStarProjection
      [(0, Real.pi), (Real.pi, 0)] : QubitSpace →L[ℂ] QubitSpace)
      (rationalState : QubitSpace) = WithLp.toLp 2 ![(3 / 5 : ℂ), (-4 / 5 : ℂ)] := by
  refine ⟨?_, ?_, ?_, rationalState_reverse_phase_order⟩
  · rw [rationalState_physical_bad_recurrence, phaseRecurrence_split_cubic]
    norm_num [FixedPoint.badPhase]
  · rw [rationalState_physical_bad_recurrence, phaseRecurrence_reverse_linear]
    norm_num [FixedPoint.badPhase]
  · rw [rationalState_split_phase_order]
    exact rationalState_iterate_pi_direct

/-- The recurrence path keeps i and recovers the independently computed bad
coordinate (72+28i)/125. -/
theorem rationalState_nonreal_recurrence_bad :
    FixedPoint.badPhase [(Real.pi, Real.pi / 2)] = Complex.I ∧
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection
      [(Real.pi, Real.pi / 2)] : QubitSpace) 1 = (72 + 28 * Complex.I) / 125 := by
  constructor
  · simp [FixedPoint.badPhase, phaseFactor_half_pi]
  · rw [rationalState_physical_bad_recurrence, rationalState_nonreal_recurrence]
    simp [FixedPoint.badPhase, phaseFactor_half_pi]
    ring_nf
    simp
    ring

/-- The recurrence bridge gives the same real probabilities as the directly
computed nonreal actual vector. -/
theorem rationalState_nonreal_recurrence_weights :
    failureWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection
        [(Real.pi, Real.pi / 2)] : QubitSpace) = (5968 / 15625 : ℝ) ∧
    successWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection
        [(Real.pi, Real.pi / 2)] : QubitSpace) = (9657 / 15625 : ℝ) := by
  rw [output_failureWeight rationalState firstBasisTarget_isStarProjection,
    output_successWeight rationalState firstBasisTarget_isStarProjection,
    outputAmplitude, rationalState_reduction_amplitudes.1]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [rationalState_nonreal_recurrence, Complex.sq_norm]
  norm_num [Complex.normSq_apply]

/-- A rank-two target in dimension three uses the same recurrence formula. -/
theorem threeLevel_phaseRecurrence_probabilities (ps : List (ℝ × ℝ)) :
    failureWeight firstTwoTarget
      (FixedPoint.output threeLevelState firstTwoTarget_isStarProjection ps : ThreeLevelSpace) =
      ‖PhaseRecurrence.value (2 / 3 : ℂ) (angles ps)‖ ^ 2 ∧
    successWeight firstTwoTarget
      (FixedPoint.output threeLevelState firstTwoTarget_isStarProjection ps : ThreeLevelSpace) =
      1 - ‖PhaseRecurrence.value (2 / 3 : ℂ) (angles ps)‖ ^ 2 := by
  have hx : FixedPoint.Reduction.failureAmplitude threeLevelState firstTwoTarget = (2 / 3 : ℝ) := by
    rw [FixedPoint.Reduction.failureAmplitude, threeLevelState_success]
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  simpa [outputAmplitude, hx] using
    And.intro (output_failureWeight threeLevelState firstTwoTarget_isStarProjection ps)
      (output_successWeight threeLevelState firstTwoTarget_isStarProjection ps)

/-- The completely bad endpoint is covered by the actual recurrence theorem. -/
theorem basisOne_phaseRecurrence_boundary (ps : List (ℝ × ℝ)) :
    outputAmplitude basisOne firstBasisTarget ps = 1 ∧
    failureWeight firstBasisTarget
      (FixedPoint.output basisOne firstBasisTarget_isStarProjection ps : QubitSpace) = 1 := by
  have hs : successWeight firstBasisTarget (basisOne : QubitSpace) = 0 := by
    simp [successWeight]
  have ha : outputAmplitude basisOne firstBasisTarget ps = 1 := by
    simp [outputAmplitude, FixedPoint.Reduction.failureAmplitude, hs]
  exact ⟨ha, by rw [output_failureWeight basisOne firstBasisTarget_isStarProjection, ha]; simp⟩

/-- The completely good endpoint is covered without a normalized bad direction. -/
theorem basisZero_phaseRecurrence_boundary (ps : List (ℝ × ℝ)) :
    outputAmplitude basisZero firstBasisTarget ps = 0 ∧
    failureWeight firstBasisTarget
      (FixedPoint.output basisZero firstBasisTarget_isStarProjection ps : QubitSpace) = 0 := by
  have hs : successWeight firstBasisTarget (basisZero : QubitSpace) = 1 := by
    simp [successWeight]
  have hv : PhaseRecurrence.value 0 (angles ps) = 0 :=
    PhaseRecurrence.value_zero_of_length_eq_twice (angles ps) ps.length (angles_length ps)
  have ha : outputAmplitude basisZero firstBasisTarget ps = 0 := by
    simpa [outputAmplitude, FixedPoint.Reduction.failureAmplitude, hs] using hv
  exact ⟨ha, by rw [output_failureWeight basisZero firstBasisTarget_isStarProjection, ha]; simp⟩

/-- One P14 step retains its minus sign after converting the parameters. -/
theorem rationalState_p14_singleton_recurrence (α β : ℝ) :
    (1 - firstBasisTarget)
      ((FixedPoint.p14Execute rationalState firstBasisTarget_isStarProjection [(α, β)] :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      (-(FixedPoint.badPhase [(β, -α)] *
        outputAmplitude rationalState firstBasisTarget [(β, -α)])) •
        (basisOne : QubitSpace) := by
  simpa [FixedPoint.p14ToP24, rationalState_bad_direction] using
    p14_failure_vector rationalState firstBasisTarget_isStarProjection
      rationalState_success_pos rationalState_success_lt_one [(α, β)]

/-- Two P14 steps contribute a positive sequence sign without reversing time. -/
theorem rationalState_p14_pair_recurrence (α₁ β₁ α₂ β₂ : ℝ) :
    (1 - firstBasisTarget)
      ((FixedPoint.p14Execute rationalState firstBasisTarget_isStarProjection
        [(α₁, β₁), (α₂, β₂)] : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      (FixedPoint.badPhase [(β₁, -α₁), (β₂, -α₂)] *
        outputAmplitude rationalState firstBasisTarget [(β₁, -α₁), (β₂, -α₂)]) •
        (basisOne : QubitSpace) := by
  simpa [FixedPoint.p14ToP24, rationalState_bad_direction] using
    p14_failure_vector rationalState firstBasisTarget_isStarProjection
      rationalState_success_pos rationalState_success_lt_one [(α₁, β₁), (α₂, β₂)]

end
end QFixLean.Examples
