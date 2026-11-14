module

public import QFixLean.Basic.Projection

/-!
# Two-outcome projective measurement weights

Weights are real squared norms on general vectors. They are probabilities in
`[0,1]` only when the operator is an orthogonal projection and the input is
normalized. The same definitions apply directly to actual outputs such as `U s`.

Global phases preserve weights and normalization, while vector equality retains
the phase. This file does not define postmeasurement states.
-/

@[expose] public section

namespace QFixLean

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Squared norm in the target component; a probability when `P` is an orthogonal
projection and the input is normalized. -/
def successWeight (P : E →L[ℂ] E) (v : E) : ℝ := ‖P v‖ ^ 2

/-- Squared norm in the complementary component. -/
def failureWeight (P : E →L[ℂ] E) (v : E) : ℝ := ‖(1 - P) v‖ ^ 2

theorem successWeight_nonneg (P : E →L[ℂ] E) (v : E) : 0 ≤ successWeight P v :=
  sq_nonneg _

theorem failureWeight_nonneg (P : E →L[ℂ] E) (v : E) : 0 ≤ failureWeight P v :=
  sq_nonneg _

@[simp]
theorem successWeight_zero (v : E) : successWeight (0 : E →L[ℂ] E) v = 0 := by
  simp [successWeight]

@[simp]
theorem failureWeight_zero (v : E) : failureWeight (0 : E →L[ℂ] E) v = ‖v‖ ^ 2 := by
  simp [failureWeight]

@[simp]
theorem successWeight_one (v : E) : successWeight (1 : E →L[ℂ] E) v = ‖v‖ ^ 2 := by
  simp [successWeight]

@[simp]
theorem failureWeight_one (v : E) : failureWeight (1 : E →L[ℂ] E) v = 0 := by
  simp [failureWeight]

/-- Scaling holds for every operator, without projection or normalization assumptions. -/
theorem successWeight_smul (P : E →L[ℂ] E) (z : ℂ) (v : E) :
    successWeight P (z • v) = ‖z‖ ^ 2 * successWeight P v := by
  simp only [successWeight, map_smul, norm_smul, mul_pow]

theorem failureWeight_smul (P : E →L[ℂ] E) (z : ℂ) (v : E) :
    failureWeight P (z • v) = ‖z‖ ^ 2 * failureWeight P v :=
  successWeight_smul (1 - P) z v

theorem norm_smul_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (v : E) :
    ‖z • v‖ = ‖v‖ := by
  rw [norm_smul, hz, one_mul]

theorem successWeight_phase (P : E →L[ℂ] E) {z : ℂ} (hz : ‖z‖ = 1) (v : E) :
    successWeight P (z • v) = successWeight P v := by
  rw [successWeight_smul, hz, one_pow, one_mul]

theorem failureWeight_phase (P : E →L[ℂ] E) {z : ℂ} (hz : ‖z‖ = 1) (v : E) :
    failureWeight P (z • v) = failureWeight P v := by
  rw [failureWeight_smul, hz, one_pow, one_mul]

namespace PureState

/-- A unit-modulus scalar preserves normalization, retaining its exact phase. -/
def phase (ψ : PureState E) (z : ℂ) (hz : ‖z‖ = 1) : PureState E :=
  ⟨z • (ψ : E), (norm_smul_of_norm_eq_one hz _).trans ψ.normalized⟩

@[simp]
theorem coe_phase (ψ : PureState E) (z : ℂ) (hz : ‖z‖ = 1) :
    (ψ.phase z hz : E) = z • (ψ : E) := rfl

end PureState

variable [CompleteSpace E]

theorem successWeight_add_failureWeight {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    successWeight P v + failureWeight P v = ‖v‖ ^ 2 :=
  projection_norm_sq_add hP v

theorem successWeight_le_norm_sq {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    successWeight P v ≤ ‖v‖ ^ 2 := by
  calc
    successWeight P v ≤ successWeight P v + failureWeight P v :=
      le_add_of_nonneg_right (failureWeight_nonneg P v)
    _ = ‖v‖ ^ 2 := successWeight_add_failureWeight hP v

theorem failureWeight_le_norm_sq {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    failureWeight P v ≤ ‖v‖ ^ 2 := by
  calc
    failureWeight P v ≤ successWeight P v + failureWeight P v :=
      le_add_of_nonneg_left (successWeight_nonneg P v)
    _ = ‖v‖ ^ 2 := successWeight_add_failureWeight hP v

theorem successWeight_add_failureWeight_of_norm_eq_one {P : E →L[ℂ] E}
    (hP : IsStarProjection P) {v : E} (hv : ‖v‖ = 1) :
    successWeight P v + failureWeight P v = 1 := by
  rw [successWeight_add_failureWeight hP, hv, one_pow]

theorem successWeight_mem_Icc_of_norm_eq_one {P : E →L[ℂ] E}
    (hP : IsStarProjection P) {v : E} (hv : ‖v‖ = 1) :
    successWeight P v ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact successWeight_nonneg P v
  · simpa only [hv, one_pow] using successWeight_le_norm_sq hP v

theorem failureWeight_mem_Icc_of_norm_eq_one {P : E →L[ℂ] E}
    (hP : IsStarProjection P) {v : E} (hv : ‖v‖ = 1) :
    failureWeight P v ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact failureWeight_nonneg P v
  · simpa only [hv, one_pow] using failureWeight_le_norm_sq hP v

/-- Probability overlap, with the real weight explicitly embedded in `ℂ`. -/
theorem inner_projection_eq_successWeight {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    inner ℂ v (P v) = (successWeight P v : ℂ) :=
  inner_projection_eq_norm_sq hP v

theorem inner_complement_eq_failureWeight {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    inner ℂ v ((1 - P) v) = (failureWeight P v : ℂ) :=
  inner_complement_eq_norm_sq hP v

namespace PureState

theorem successWeight_add_failureWeight {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ψ : PureState E) :
    QFixLean.successWeight P (ψ : E) + QFixLean.failureWeight P (ψ : E) = 1 :=
  successWeight_add_failureWeight_of_norm_eq_one hP ψ.normalized

theorem successWeight_mem_Icc {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : PureState E) :
    QFixLean.successWeight P (ψ : E) ∈ Set.Icc (0 : ℝ) 1 :=
  successWeight_mem_Icc_of_norm_eq_one hP ψ.normalized

theorem failureWeight_mem_Icc {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : PureState E) :
    QFixLean.failureWeight P (ψ : E) ∈ Set.Icc (0 : ℝ) 1 :=
  failureWeight_mem_Icc_of_norm_eq_one hP ψ.normalized

end PureState
end
end QFixLean
