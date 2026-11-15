module

public import QFixLean.FixedPoint.PhaseSequence
import Mathlib.Tactic.Linarith

/-!
# Degenerate inputs of an arbitrary phase sequence

These results apply to the actual execution without normalizing a zero
component. The scalar phases are explicit products of the same sequence's
angles. They do not imply any fixed-point guarantee for nondegenerate inputs.
-/

@[expose] public section

namespace QFixLean.FixedPoint

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The phase accumulated by a completely bad initial input. -/
def badPhase : List (ℝ × ℝ) → ℂ
  | [] => 1
  | p :: ps => phaseFactor p.2 * badPhase ps

/-- The phase accumulated by a completely good initial input. -/
def goodPhase : List (ℝ × ℝ) → ℂ
  | [] => 1
  | p :: ps => phaseFactor (p.1 + p.2) * goodPhase ps

theorem badPhase_norm (ps : List (ℝ × ℝ)) : ‖badPhase ps‖ = 1 := by
  induction ps with
  | nil => simp [badPhase]
  | cons p ps ih => simp only [badPhase, norm_mul, phaseFactor_norm, ih, one_mul]

theorem goodPhase_norm (ps : List (ℝ × ℝ)) : ‖goodPhase ps‖ = 1 := by
  induction ps with
  | nil => simp [goodPhase]
  | cons p ps ih => simp only [goodPhase, norm_mul, phaseFactor_norm, ih, one_mul]

theorem badPhase_eq_sum (ps : List (ℝ × ℝ)) :
    badPhase ps = phaseFactor ((ps.map Prod.snd).sum) := by
  induction ps with
  | nil => simp [badPhase]
  | cons p ps ih => simp only [badPhase, List.map_cons, List.sum_cons, phaseFactor_add, ih]

theorem goodPhase_eq_sum (ps : List (ℝ × ℝ)) :
    goodPhase ps = phaseFactor ((ps.map (fun p => p.1 + p.2)).sum) := by
  induction ps with
  | nil => simp [goodPhase]
  | cons p ps ih => simp only [goodPhase, List.map_cons, List.sum_cons, phaseFactor_add, ih]

omit [CompleteSpace E] in
theorem projection_eq_zero_of_success_zero (ψ₀ : PureState E) (P : E →L[ℂ] E)
    (hs : successWeight P (ψ₀ : E) = 0) : P (ψ₀ : E) = 0 :=
  norm_eq_zero.mp (sq_eq_zero_iff.mp hs)

theorem complement_eq_zero_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1) :
    (1 - P) (ψ₀ : E) = 0 := by
  have hc := ψ₀.successWeight_add_failureWeight hP
  have hf : failureWeight P (ψ₀ : E) = 0 := by linarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hf)

theorem projection_eq_self_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1) :
    P (ψ₀ : E) = (ψ₀ : E) := by
  have hc := complement_eq_zero_of_success_one ψ₀ hP hs
  have hsub : (ψ₀ : E) - P (ψ₀ : E) = 0 := by
    simpa only [sub_apply, one_apply_eq_self] using hc
  exact (sub_eq_zero.mp hsub).symm

theorem iterate_of_success_zero (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 0) (α β : ℝ) :
    (iterate ψ₀ hP α β : E →L[ℂ] E) (ψ₀ : E) = phaseFactor β • (ψ₀ : E) := by
  have hp := projection_eq_zero_of_success_zero ψ₀ P hs
  change phaseRotation ψ₀.projection β (phaseRotation P α (ψ₀ : E)) = _
  have ht : phaseRotation P α (ψ₀ : E) = (ψ₀ : E) :=
    selectivePhase_of_mem_ker hp (phaseFactor α)
  rw [ht]
  exact ψ₀.phaseRotation_projection_self β

theorem iterate_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1) (α β : ℝ) :
    (iterate ψ₀ hP α β : E →L[ℂ] E) (ψ₀ : E) =
      phaseFactor (α + β) • (ψ₀ : E) := by
  have hp := projection_eq_self_of_success_one ψ₀ hP hs
  change phaseRotation ψ₀.projection β (phaseRotation P α (ψ₀ : E)) = _
  have ht : phaseRotation P α (ψ₀ : E) = phaseFactor α • (ψ₀ : E) :=
    selectivePhase_of_fixed hp (phaseFactor α)
  rw [ht, map_smul, ψ₀.phaseRotation_projection_self, smul_smul, phaseFactor_add]

theorem execute_of_success_zero (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 0)
    (ps : List (ℝ × ℝ)) :
    (execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E) = badPhase ps • (ψ₀ : E) := by
  induction ps with
  | nil => simp [badPhase]
  | cons p ps ih =>
    change (execute ψ₀ hP ps : E →L[ℂ] E)
      ((iterate ψ₀ hP p.1 p.2 : E →L[ℂ] E) (ψ₀ : E)) = _
    rw [iterate_of_success_zero ψ₀ hP hs, map_smul, ih, smul_smul]
    rfl

theorem execute_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1)
    (ps : List (ℝ × ℝ)) :
    (execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E) = goodPhase ps • (ψ₀ : E) := by
  induction ps with
  | nil => simp [goodPhase]
  | cons p ps ih =>
    change (execute ψ₀ hP ps : E →L[ℂ] E)
      ((iterate ψ₀ hP p.1 p.2 : E →L[ℂ] E) (ψ₀ : E)) = _
    rw [iterate_of_success_one ψ₀ hP hs, map_smul, ih, smul_smul]
    rfl

theorem execute_projection_of_success_zero (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 0)
    (ps : List (ℝ × ℝ)) :
    P ((execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) = 0 := by
  rw [execute_of_success_zero ψ₀ hP hs, map_smul,
    projection_eq_zero_of_success_zero ψ₀ P hs, smul_zero]

theorem execute_complement_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1)
    (ps : List (ℝ × ℝ)) :
    (1 - P) ((execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) = 0 := by
  rw [execute_of_success_one ψ₀ hP hs, map_smul,
    complement_eq_zero_of_success_one ψ₀ hP hs, smul_zero]

theorem execute_probabilities_of_success_zero (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 0)
    (ps : List (ℝ × ℝ)) :
    successWeight P ((execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) = 0 ∧
    failureWeight P ((execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) = 1 := by
  have hf : failureWeight P (ψ₀ : E) = 1 := by
    have hc := ψ₀.successWeight_add_failureWeight hP
    linarith
  rw [execute_of_success_zero ψ₀ hP hs,
    successWeight_phase P (badPhase_norm ps), failureWeight_phase P (badPhase_norm ps)]
  exact ⟨hs, hf⟩

theorem execute_probabilities_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1)
    (ps : List (ℝ × ℝ)) :
    successWeight P ((execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) = 1 ∧
    failureWeight P ((execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)) = 0 := by
  have hf : failureWeight P (ψ₀ : E) = 0 := by
    have hc := ψ₀.successWeight_add_failureWeight hP
    linarith
  rw [execute_of_success_one ψ₀ hP hs,
    successWeight_phase P (goodPhase_norm ps), failureWeight_phase P (goodPhase_norm ps)]
  exact ⟨hs, hf⟩

end
end QFixLean.FixedPoint
