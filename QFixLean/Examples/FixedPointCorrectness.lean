module

public import QFixLean.FixedPoint.Correctness
public import QFixLean.Examples.FixedPointRecurrence
public import QFixLean.Examples.QuasiChebyshevIdentity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact checks of the explicit fixed-point search

The nontrivial length-three physical output is calculated from the selective
operators, independently of the algorithm's general correctness theorem.
Physical coordinates are target, bad. Both actual phase factors have positive
imaginary part; replacing them by their conjugates changes the output vector.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

open FixedPoint.ExplicitPhases

private theorem cubicTangent_half : cubicTangent (1 / 2) = 3 / 2 := by
  have hs := cubicTangent_sq (1 / 2) (by norm_num) (by norm_num)
  have hn : 0 ≤ cubicTangent (1 / 2) := by
    rw [cubicTangent, Real.tan_pi_div_three]
    positivity
  nlinarith

/-- Both physical phases equal `(5+12i)/13`; the sign is checked exactly. -/
theorem explicit_half_phase_factors :
    phaseFactor (pair 1 (1 / 2) 1).1 = (5 + 12 * Complex.I) / 13 ∧
    phaseFactor (pair 1 (1 / 2) 1).2 = (5 + 12 * Complex.I) / 13 := by
  have hp : phaseFactor (-(2 * Real.arctan (3 / 2))) =
      (-5 - 12 * Complex.I) / 13 := by
    rw [QuasiChebyshev.phaseFactor_neg_two_arctan]
    apply (div_eq_iff (QuasiChebyshev.one_add_I_mul_ne_zero (3 / 2))).2
    norm_num
    ring_nf
    simp
    ring
  have ha : (pair 1 (1 / 2) 1).1 = Real.pi + -(2 * Real.arctan (3 / 2)) := by
    simp only [pair, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
      QuasiChebyshev.angle, cubic_tangent_one, cubicTangent_half]
    ring
  have hb : (pair 1 (1 / 2) 1).2 = -(2 * Real.arctan (3 / 2)) + -Real.pi := by
    simp only [pair, Nat.reduceMul, Nat.reduceAdd,
      QuasiChebyshev.angle, cubic_tangent_two, cubicTangent_half, Real.arctan_neg]
    ring
  rw [ha, hb, phaseFactor_add, phaseFactor_add, hp]
  simp [phaseFactor_neg]
  ring

/-- Direct expansion of the actual physical phases, retaining the full vector. -/
theorem rationalState_explicit_half_direct :
    (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
      (pair 1 (1 / 2) 1).1 (pair 1 (1 / 2) 1).2 :
        QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
      WithLp.toLp 2 ![((-5085 + 18216 * Complex.I) / 21125 : ℂ),
        ((3620 + 8688 * Complex.I) / 21125 : ℂ)] := by
  simp only [FixedPoint.coe_iterate, mul_apply_eq_comp,
    phaseRotation, explicit_half_phase_factors.1, explicit_half_phase_factors.2]
  simp only [selectivePhase_apply]
  ext i
  fin_cases i <;>
    norm_num [sub_apply, firstBasisTarget_apply, PureState.projection_apply,
      rationalState, PiLp.inner_apply, Fin.sum_univ_two, map_ofNat] <;>
    ring_nf <;> simp <;> ring

/-- The two probabilities are computed from that same exact physical vector. -/
theorem rationalState_explicit_half_weights_direct :
    failureWeight firstBasisTarget
      ((FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
        (pair 1 (1 / 2) 1).1 (pair 1 (1 / 2) 1).2 :
          QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      (724 / 1625 : ℝ) ^ 2 ∧
    successWeight firstBasisTarget
      ((FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
        (pair 1 (1 / 2) 1).1 (pair 1 (1 / 2) 1).2 :
          QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace)) =
      1 - (724 / 1625 : ℝ) ^ 2 := by
  rw [rationalState_explicit_half_direct]
  norm_num [successWeight, failureWeight, firstBasisTarget_apply, sub_apply,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]

/-- The direct physical example is outside this promise interval. -/
theorem rationalState_half_outside_promise :
    successWeight firstBasisTarget (rationalState : QubitSpace) < 1 - (1 / 2 : ℝ)^2 := by
  rw [rationalState_success]
  norm_num

/-- Independently expand the first two time-ordered physical pairs. -/
theorem explicit_two_schedule (γ : ℝ) :
    schedule 2 γ = [pair 2 γ 1, pair 2 γ 2] ∧
    FixedPoint.AmplitudeRecurrence.angles (schedule 2 γ) =
      [QuasiChebyshev.angle 5 γ 1, QuasiChebyshev.angle 5 γ 2,
       QuasiChebyshev.angle 5 γ 3, QuasiChebyshev.angle 5 γ 4] := by
  constructor
  · rfl
  · simp [schedule, List.range_succ, pair]

/-- Reverse phase matching changes indices, not time order. -/
theorem explicit_two_p14_schedule (γ : ℝ) :
    p14Schedule 2 γ =
      [(p14Source 2 γ 1, -p14Source 2 γ 2),
       (p14Source 2 γ 2, -p14Source 2 γ 1)] := rfl

/-- The empty actual execution returns the prepared state. -/
theorem rationalState_explicit_zero (γ : ℝ) :
    (FixedPoint.output rationalState firstBasisTarget_isStarProjection (schedule 0 γ) :
      QubitSpace) = (rationalState : QubitSpace) ∧
    failureWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection (schedule 0 γ) :
        QubitSpace) = 16 / 25 ∧
    successWeight firstBasisTarget
      (FixedPoint.output rationalState firstBasisTarget_isStarProjection (schedule 0 γ) :
        QubitSpace) = 9 / 25 :=
  ⟨rfl, rationalState_failure, rationalState_success⟩

/-- Two actual steps act as the second iterate times the first, with fixed source. -/
theorem explicit_two_execute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ψ₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (γ : ℝ) :
    FixedPoint.execute ψ₀ hP (schedule 2 γ) =
      FixedPoint.iterate ψ₀ hP (pair 2 γ 2).1 (pair 2 γ 2).2 *
      FixedPoint.iterate ψ₀ hP (pair 2 γ 1).1 (pair 2 γ 1).2 := by
  rw [(explicit_two_schedule γ).1, FixedPoint.execute_pair]

/-- At gamma one the physical singleton is exactly the ordinary Grover pair. -/
theorem explicit_gamma_one_iterate :
    FixedPoint.execute rationalState firstBasisTarget_isStarProjection (schedule 1 1) =
      FixedPoint.iterate rationalState firstBasisTarget_isStarProjection Real.pi Real.pi := by
  apply Subtype.ext
  simp [schedule, List.range_succ, pair, FixedPoint.coe_iterate,
    phaseRotation, phaseFactor_neg]

/-- A direct Grover vector check retains the distinction between P14 and P24. -/
theorem rationalState_explicit_gamma_one_direct :
    (FixedPoint.execute rationalState firstBasisTarget_isStarProjection (schedule 1 1) :
      QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
        WithLp.toLp 2 ![(-117 / 125 : ℂ), (44 / 125 : ℂ)] ∧
    (FixedPoint.p14Execute rationalState firstBasisTarget_isStarProjection
      (p14Schedule 1 1) : QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) =
        WithLp.toLp 2 ![(117 / 125 : ℂ), (-44 / 125 : ℂ)] := by
  constructor
  · rw [explicit_gamma_one_iterate, rationalState_iterate_pi_direct]
  · rw [p14Execute_schedule_coe, explicit_gamma_one_iterate]
    simp only [pow_one, smul_apply, rationalState_iterate_pi_direct]
    ext i
    fin_cases i <;> norm_num

/-- Actual P14 and P24 global factors at zero, one, and two steps. -/
theorem explicit_short_global_phases {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ψ₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (γ : ℝ) :
    (FixedPoint.p14Execute ψ₀ hP (p14Schedule 0 γ) : E →L[ℂ] E) = 1 ∧
    (FixedPoint.p14Execute ψ₀ hP (p14Schedule 1 γ) : E →L[ℂ] E) =
      -(FixedPoint.execute ψ₀ hP (schedule 1 γ) : E →L[ℂ] E) ∧
    (FixedPoint.p14Execute ψ₀ hP (p14Schedule 2 γ) : E →L[ℂ] E) =
      (FixedPoint.execute ψ₀ hP (schedule 2 γ) : E →L[ℂ] E) := by
  simp [p14Execute_schedule_coe]

/-- The same actual singleton is identified before the independent paths meet. -/
theorem rationalState_explicit_half_search_eq :
    (search rationalState firstBasisTarget_isStarProjection 1 (1 / 2) : QubitSpace) =
      (FixedPoint.iterate rationalState firstBasisTarget_isStarProjection
        (pair 1 (1 / 2) 1).1 (pair 1 (1 / 2) 1).2 :
          QubitSpace →L[ℂ] QubitSpace) (rationalState : QubitSpace) := rfl

/-- The independent operator path proves the actual search's exact weights. -/
theorem rationalState_explicit_half_weights_operator :
    failureWeight firstBasisTarget
      (search rationalState firstBasisTarget_isStarProjection 1 (1 / 2) : QubitSpace) =
      (724 / 1625 : ℝ) ^ 2 ∧
    successWeight firstBasisTarget
      (search rationalState firstBasisTarget_isStarProjection 1 (1 / 2) : QubitSpace) =
      1 - (724 / 1625 : ℝ) ^ 2 := by
  rw [rationalState_explicit_half_search_eq]
  exact rationalState_explicit_half_weights_direct

/-- A second path uses the complete algorithm theorem and evaluates Mathlib's T₃. -/
theorem rationalState_explicit_half_weights_formula :
    failureWeight firstBasisTarget
      (search rationalState firstBasisTarget_isStarProjection 1 (1 / 2) : QubitSpace) =
      (724 / 1625 : ℝ) ^ 2 ∧
    successWeight firstBasisTarget
      (search rationalState firstBasisTarget_isStarProjection 1 (1 / 2) : QubitSpace) =
      1 - (724 / 1625 : ℝ) ^ 2 := by
  rw [search_failureWeight rationalState firstBasisTarget_isStarProjection 1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num),
    search_successWeight rationalState firstBasisTarget_isStarProjection 1
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num),
    rationalState_reduction_amplitudes.1]
  norm_num [Chebyshev.amplitude, Chebyshev.denominator, chebyshev_evalT_three]

/-- The signed amplitude is positive here, before its square is taken. -/
theorem rationalState_explicit_half_amplitude :
    FixedPoint.AmplitudeRecurrence.outputAmplitude rationalState firstBasisTarget
      (schedule 1 (1 / 2)) = (724 / 1625 : ℂ) := by
  rw [outputAmplitude_schedule rationalState firstBasisTarget 1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num),
    rationalState_reduction_amplitudes.1]
  norm_num [Chebyshev.amplitude, Chebyshev.denominator, chebyshev_evalT_three]

/-- Negative sign-sensitive scalar validation remains visible at the physical
schedule's extracted recurrence angles; no corresponding quantum state is assumed. -/
theorem explicit_half_quarter_negative :
    PhaseRecurrence.value (1 / 4 : ℂ)
      (FixedPoint.AmplitudeRecurrence.angles (schedule 1 (1 / 2))) = -(1 / 26 : ℂ) := by
  rw [angles_schedule]
  exact quasi_cubic_half_quarter_direct

/-- Initial success zero remains zero for every explicit list, including gamma one. -/
theorem basisOne_explicit_probabilities (ℓ : ℕ) (γ : ℝ) :
    successWeight firstBasisTarget
      (search basisOne firstBasisTarget_isStarProjection ℓ γ : QubitSpace) = 0 ∧
    failureWeight firstBasisTarget
      (search basisOne firstBasisTarget_isStarProjection ℓ γ : QubitSpace) = 1 :=
  basisOne_fixedPoint_probabilities (schedule ℓ γ)

/-- Initial success one is covered without ever dividing by its zero bad component. -/
theorem basisZero_explicit_probabilities (ℓ : ℕ) (γ : ℝ) :
    successWeight firstBasisTarget
      (search basisZero firstBasisTarget_isStarProjection ℓ γ : QubitSpace) = 1 ∧
    failureWeight firstBasisTarget
      (search basisZero firstBasisTarget_isStarProjection ℓ γ : QubitSpace) = 0 :=
  basisZero_fixedPoint_probabilities (schedule ℓ γ)

/-- The formula applies to a rank-two target in a three-dimensional space. -/
theorem threeLevel_explicit_probabilities (ℓ : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    failureWeight firstTwoTarget
      (search threeLevelState firstTwoTarget_isStarProjection ℓ γ : ThreeLevelSpace) =
      Chebyshev.amplitude (2 * ℓ + 1) γ (2 / 3) ^ 2 ∧
    successWeight firstTwoTarget
      (search threeLevelState firstTwoTarget_isStarProjection ℓ γ : ThreeLevelSpace) =
      1 - Chebyshev.amplitude (2 * ℓ + 1) γ (2 / 3) ^ 2 := by
  have hx : FixedPoint.Reduction.failureAmplitude threeLevelState firstTwoTarget = 2 / 3 := by
    rw [FixedPoint.Reduction.failureAmplitude, threeLevelState_success]
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [search_failureWeight threeLevelState firstTwoTarget_isStarProjection ℓ hγ hγ1,
    search_successWeight threeLevelState firstTwoTarget_isStarProjection ℓ hγ hγ1, hx]
  exact ⟨rfl, rfl⟩

/-- The rational state exactly saturates the degree-one standard promise boundary. -/
theorem rationalState_explicit_threshold :
    failureWeight firstBasisTarget
      (parameterSearch rationalState firstBasisTarget_isStarProjection 0 (4 / 5) :
        QubitSpace) = (4 / 5 : ℝ)^2 ∧
    failureWeight firstBasisTarget
      (p14ParameterSearch rationalState firstBasisTarget_isStarProjection 0 (4 / 5) :
        QubitSpace) = (4 / 5 : ℝ)^2 := by
  have hp : successWeight firstBasisTarget (rationalState : QubitSpace) =
      1 - (Chebyshev.parameter (2 * 0 + 1) (4 / 5))^2 := by
    rw [rationalState_success]
    norm_num [Chebyshev.parameter_one (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num)]
  exact ⟨parameterSearch_failureWeight_at_threshold rationalState
      firstBasisTarget_isStarProjection 0 (by norm_num) (by norm_num) hp,
    p14ParameterSearch_failureWeight_at_threshold rationalState
      firstBasisTarget_isStarProjection 0 (by norm_num) (by norm_num) hp⟩

end
end QFixLean.Examples
