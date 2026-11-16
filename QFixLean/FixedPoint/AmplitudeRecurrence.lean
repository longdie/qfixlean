module

public import QFixLean.FixedPoint.Interleaved
public import QFixLean.FixedPoint.Reduction
public import QFixLean.FixedPoint.PhaseConventions
import Mathlib.Tactic.Linarith

/-!
# Actual phase execution and the second-order failure-amplitude recurrence

Reference: P24, arXiv:2403.02057v3, Section 3.2 (PDF Lemma 2, HTML
Lemma 3.2). `Interleaved` proves the matrix and scalar recurrence bridge;
this file applies it to the same actual execution defined in `PhaseSequence`.
The target has arbitrary rank. Only the normalized-direction vector equalities
need a nondegenerate initial success probability. The final probability
identities include both endpoints and retain no formula premise.

This recurrence is general. `FixedPoint.Correctness` identifies the explicit
P14/P24 schedule with a Chebyshev ratio through the proved terminal identity.
-/

@[expose] public section

namespace QFixLean.FixedPoint.AmplitudeRecurrence

noncomputable section

open Reduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The terminal second-order amplitude, with the actual initial failure
magnitude supplied as its argument. For `ℓ` steps its index is `2 * ℓ + 1`. -/
def outputAmplitude (ψ₀ : PureState E) (P : E →L[ℂ] E) (ps : List (ℝ × ℝ)) : ℂ :=
  PhaseRecurrence.value (failureAmplitude ψ₀ P : ℂ) (angles ps)

/-- The terminal complex polynomial. Its coefficients depend on the phases,
not on the actual input's success probability. -/
def outputPolynomial (ps : List (ℝ × ℝ)) : Polynomial ℂ :=
  PhaseRecurrence.polynomial (angles ps)

variable (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)

omit [CompleteSpace E] in
/-- The polynomial evaluation is the terminal scalar used below. -/
theorem outputPolynomial_eval (ps : List (ℝ × ℝ)) :
    (outputPolynomial ps).eval (failureAmplitude ψ₀ P : ℂ) =
      outputAmplitude ψ₀ P ps :=
  PhaseRecurrence.polynomial_eval _ _

include hP in
/-- The exact bad coordinate, including the accumulated source phase. -/
theorem outputCoordinates_bad (ps : List (ℝ × ℝ)) :
    outputCoordinates ψ₀ P ps 0 = badPhase ps * outputAmplitude ψ₀ P ps := by
  have h := matrix_output_recurrence (amplitude_sq_add ψ₀ hP) ps
  have hc := congrArg (fun v : TwoDimensional.Coord => v 0) h
  simpa only [outputCoordinates, outputAmplitude, PiLp.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero] using hc

/-- The canonical coordinates describe the same actual output. The vector
equality retains the full phase before any measurement is taken. -/
theorem output_eq_recurrence (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    (output ψ₀ hP ps : E) = badPhase ps •
      embed ψ₀ P (WithLp.toLp 2 ![outputAmplitude ψ₀ P ps,
        (successAmplitude ψ₀ P : ℂ) * (finalCoupled (failureAmplitude ψ₀ P : ℂ) ps).2]) := by
  rw [output_eq_embed ψ₀ hP h0 h1]
  unfold outputCoordinates
  rw [matrix_output_recurrence (amplitude_sq_add ψ₀ hP) ps, map_smul]
  rfl

/-- Exact complementary component of the actual output in its unit bad
direction. No global phase is discarded in this equality. -/
theorem output_failure_vector (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    (1 - P) (output ψ₀ hP ps : E) =
      (badPhase ps * outputAmplitude ψ₀ P ps) • badDirection ψ₀ P := by
  rw [output_eq_embed ψ₀ hP h0 h1, complement_embed_components ψ₀ hP,
    outputCoordinates_bad ψ₀ hP]

theorem output_failure_norm (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    ‖(1 - P) (output ψ₀ hP ps : E)‖ = ‖outputAmplitude ψ₀ P ps‖ := by
  rw [output_failure_vector ψ₀ hP h0 h1, norm_smul, norm_mul,
    badPhase_norm, norm_badDirection ψ₀ hP h1, one_mul, mul_one]

theorem output_failureWeight_nondegenerate (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    failureWeight P (output ψ₀ hP ps : E) = ‖outputAmplitude ψ₀ P ps‖ ^ 2 := by
  unfold failureWeight
  rw [output_failure_norm ψ₀ hP h0 h1]

/-- General actual-output probability formula. Endpoint inputs use the
existing execution boundary results, without normalizing zero components. -/
theorem output_failureWeight (ps : List (ℝ × ℝ)) :
    failureWeight P (output ψ₀ hP ps : E) = ‖outputAmplitude ψ₀ P ps‖ ^ 2 := by
  have hr := ψ₀.successWeight_mem_Icc hP
  by_cases hz : successWeight P (ψ₀ : E) = 0
  · have hf := (execute_probabilities_of_success_zero ψ₀ hP hz ps).2
    simpa [outputAmplitude, failureAmplitude, hz, PhaseRecurrence.value_one] using hf
  · by_cases ho : successWeight P (ψ₀ : E) = 1
    · have hf := (execute_probabilities_of_success_one ψ₀ hP ho ps).2
      have hv : PhaseRecurrence.value 0 (angles ps) = 0 :=
        PhaseRecurrence.value_zero_of_length_eq_twice (angles ps) ps.length (angles_length ps)
      simpa [outputAmplitude, failureAmplitude, ho, hv] using hf
    · exact output_failureWeight_nondegenerate ψ₀ hP
        (lt_of_le_of_ne hr.1 (Ne.symm hz)) (lt_of_le_of_ne hr.2 ho) ps

/-- Success is the complement of the recurrence modulus squared for the
same normalized actual output. -/
theorem output_successWeight (ps : List (ℝ × ℝ)) :
    successWeight P (output ψ₀ hP ps : E) = 1 - ‖outputAmplitude ψ₀ P ps‖ ^ 2 := by
  have h := (output ψ₀ hP ps).successWeight_add_failureWeight hP
  rw [output_failureWeight ψ₀ hP ps] at h
  linarith

/-- The actual failure probability is the evaluated terminal polynomial's
modulus squared, including initial success zero or one. -/
theorem output_failureWeight_polynomial (ps : List (ℝ × ℝ)) :
    failureWeight P (output ψ₀ hP ps : E) =
      ‖(outputPolynomial ps).eval (failureAmplitude ψ₀ P : ℂ)‖ ^ 2 := by
  rw [outputPolynomial_eval, output_failureWeight ψ₀ hP]

theorem output_successWeight_polynomial (ps : List (ℝ × ℝ)) :
    successWeight P (output ψ₀ hP ps : E) =
      1 - ‖(outputPolynomial ps).eval (failureAmplitude ψ₀ P : ℂ)‖ ^ 2 := by
  rw [outputPolynomial_eval, output_successWeight ψ₀ hP]

/-- P14's actual failure component has both its sequence sign and the
converted P24 source phase. -/
theorem p14_failure_vector (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    (1 - P) ((p14Execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) =
      (((-1 : ℂ) ^ ps.length * badPhase (ps.map p14ToP24)) *
        outputAmplitude ψ₀ P (ps.map p14ToP24)) • badDirection ψ₀ P := by
  rw [p14Execute_apply_eq, map_smul]
  change ((-1 : ℂ) ^ ps.length) • (1 - P) (output ψ₀ hP (ps.map p14ToP24) : E) = _
  rw [output_failure_vector ψ₀ hP h0 h1, smul_smul, mul_assoc]

theorem p14_failureWeight (ps : List (ℝ × ℝ)) :
    failureWeight P ((p14Execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) =
      ‖outputAmplitude ψ₀ P (ps.map p14ToP24)‖ ^ 2 := by
  rw [p14Execute_failureWeight]
  exact output_failureWeight ψ₀ hP _

theorem p14_successWeight (ps : List (ℝ × ℝ)) :
    successWeight P ((p14Execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) =
      1 - ‖outputAmplitude ψ₀ P (ps.map p14ToP24)‖ ^ 2 := by
  rw [p14Execute_successWeight]
  exact output_successWeight ψ₀ hP _

end
end QFixLean.FixedPoint.AmplitudeRecurrence
