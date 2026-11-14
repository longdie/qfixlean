module

public import QFixLean.Basic.Phase
public import QFixLean.Basic.PhaseFactor
public import QFixLean.Basic.Unitary
import Mathlib.Tactic.Module

/-!
# Selective phases with real angles

`phaseRotation P φ` multiplies the target component by `exp (I * φ)` and
preserves the complement. The same operator acts on general target subspaces
and normalized source-state projections. Its bundled unitary uses exactly
this underlying operator, so it can act through `PureState.map`.
-/

@[expose] public section

namespace QFixLean

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Selective phase with the positive real-angle convention `exp (I * φ)`. -/
def phaseRotation (P : E →L[ℂ] E) (φ : ℝ) : E →L[ℂ] E :=
  selectivePhase P (phaseFactor φ)

theorem phaseRotation_apply_components (P : E →L[ℂ] E) (φ : ℝ) (v : E) :
    phaseRotation P φ v = (1 - P) v + phaseFactor φ • P v :=
  selectivePhase_apply_components P (phaseFactor φ) v

@[simp]
theorem phaseRotation_zero (P : E →L[ℂ] E) : phaseRotation P 0 = 1 := by
  simp [phaseRotation]

@[simp]
theorem phaseRotation_zero_target (φ : ℝ) : phaseRotation (0 : E →L[ℂ] E) φ = 1 := by
  simp [phaseRotation]

@[simp]
theorem phaseRotation_one_target (φ : ℝ) :
    phaseRotation (1 : E →L[ℂ] E) φ = phaseFactor φ • (1 : E →L[ℂ] E) := by
  simp [phaseRotation]

/-- Addition of angles composes phases on the same idempotent target. -/
theorem phaseRotation_add {P : E →L[ℂ] E} (hP : IsIdempotentElem P) (φ θ : ℝ) :
    phaseRotation P φ * phaseRotation P θ = phaseRotation P (φ + θ) := by
  simp only [phaseRotation, selectivePhase_mul hP, phaseFactor_add]

theorem phaseRotation_neg_mul {P : E →L[ℂ] E} (hP : IsIdempotentElem P) (φ : ℝ) :
    phaseRotation P (-φ) * phaseRotation P φ = 1 := by
  rw [phaseRotation_add hP, neg_add_cancel, phaseRotation_zero]

theorem phaseRotation_mul_neg {P : E →L[ℂ] E} (hP : IsIdempotentElem P) (φ : ℝ) :
    phaseRotation P φ * phaseRotation P (-φ) = 1 := by
  rw [phaseRotation_add hP, add_neg_cancel, phaseRotation_zero]

/-- At π the target component changes sign and the complement is preserved. -/
theorem phaseRotation_pi (P : E →L[ℂ] E) :
    phaseRotation P Real.pi = 1 - (2 : ℂ) • P := by
  simp only [phaseRotation, phaseFactor_pi, selectivePhase]
  module

theorem phaseRotation_pi_mul_self {P : E →L[ℂ] E} (hP : IsIdempotentElem P) :
    phaseRotation P Real.pi * phaseRotation P Real.pi = 1 := by
  simp only [phaseRotation, phaseFactor_pi]
  rw [selectivePhase_mul hP]
  simp

namespace PureState

theorem phaseRotation_projection_self (s : PureState E) (φ : ℝ) :
    phaseRotation s.projection φ (s : E) = phaseFactor φ • (s : E) :=
  s.selectivePhase_projection_self (phaseFactor φ)

theorem phaseRotation_projection_of_inner_eq_zero (s : PureState E) {v : E}
    (hv : inner ℂ (s : E) v = 0) (φ : ℝ) : phaseRotation s.projection φ v = v :=
  s.selectivePhase_projection_of_inner_eq_zero hv (phaseFactor φ)

end PureState

variable [CompleteSpace E]

theorem successWeight_phaseRotation {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (φ : ℝ) (v : E) : successWeight P (phaseRotation P φ v) = successWeight P v :=
  successWeight_selectivePhase hP.isIdempotentElem (phaseFactor_norm φ) v

theorem failureWeight_phaseRotation {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (φ : ℝ) (v : E) : failureWeight P (phaseRotation P φ v) = failureWeight P v :=
  failureWeight_selectivePhase hP.isIdempotentElem (phaseFactor φ) v

theorem star_phaseRotation {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) (φ : ℝ) :
    star (phaseRotation P φ) = phaseRotation P (-φ) := by
  rw [phaseRotation, star_selectivePhase hP, ← phaseFactor_neg]
  rfl

theorem phaseRotation_mem_unitary {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) :
    phaseRotation P φ ∈ unitary (E →L[ℂ] E) :=
  selectivePhase_mem_unitary hP (phaseFactor_star_mul_self φ)

/-- The native unitary with underlying operator `phaseRotation P φ`. -/
def phaseRotationUnitary {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) :
    unitary (E →L[ℂ] E) :=
  ⟨phaseRotation P φ, phaseRotation_mem_unitary hP φ⟩

@[simp]
theorem coe_phaseRotationUnitary {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) :
    (phaseRotationUnitary hP φ : E →L[ℂ] E) = phaseRotation P φ := rfl

theorem star_phaseRotationUnitary {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) :
    star (phaseRotationUnitary hP φ) = phaseRotationUnitary hP (-φ) := by
  apply Subtype.ext
  exact star_phaseRotation hP.isSelfAdjoint φ

theorem phaseRotationUnitary_inv {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) :
    (phaseRotationUnitary hP φ)⁻¹ = phaseRotationUnitary hP (-φ) :=
  (Unitary.star_eq_inv _).symm.trans (star_phaseRotationUnitary hP φ)

/-- Norm preservation holds for every input vector, without normalization. -/
theorem phaseRotation_norm {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) (v : E) :
    ‖phaseRotation P φ v‖ = ‖v‖ :=
  Unitary.norm_map (phaseRotationUnitary hP φ) v

namespace PureState

/-- The source's own selective phase agrees exactly with its global phase. -/
theorem map_phaseRotation_projection_self (s : PureState E) (φ : ℝ) :
    map (phaseRotationUnitary s.isStarProjection_projection φ) s =
      s.phase (phaseFactor φ) (phaseFactor_norm φ) := by
  apply ext
  exact s.phaseRotation_projection_self φ

end PureState
end
end QFixLean
