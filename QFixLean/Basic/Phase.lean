module

public import QFixLean.Basic.Probability
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Selective phase operators

The main representation is `E →L[ℂ] E`. Multiplication acts right to left;
`star` is the adjoint. Orthogonal projections use Mathlib's mathematical
predicate `IsStarProjection`, with no restriction on their rank.

`selectivePhase P z = 1 + (z - 1) • P` multiplies the range of `P` by `z`.
The scalar parameter separates the operator algebra from the real-angle
interface in `PhaseRotation`. Unitarity requires a unit-modulus scalar.
Measurement invariance below concerns the same target projection `P`.
-/

@[expose] public section

namespace QFixLean

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Selective multiplication by `z` on the range of a projection `P`. -/
def selectivePhase (P : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E := 1 + (z - 1) • P

theorem selectivePhase_apply (P : E →L[ℂ] E) (z : ℂ) (v : E) :
    selectivePhase P z v = v + (z - 1) • P v := rfl

@[simp]
theorem selectivePhase_one (P : E →L[ℂ] E) : selectivePhase P 1 = 1 := by
  simp [selectivePhase]

@[simp]
theorem selectivePhase_zero_target (z : ℂ) : selectivePhase (0 : E →L[ℂ] E) z = 1 := by
  simp [selectivePhase]

@[simp]
theorem selectivePhase_one_target (z : ℂ) :
    selectivePhase (1 : E →L[ℂ] E) z = z • (1 : E →L[ℂ] E) := by
  unfold selectivePhase
  module

/-- The decomposition itself does not require the projection laws. -/
theorem selectivePhase_apply_components (P : E →L[ℂ] E) (z : ℂ) (v : E) :
    selectivePhase P z v = (1 - P) v + z • P v := by
  simp only [selectivePhase_apply, sub_apply, one_apply_eq_self]
  module

theorem selectivePhase_of_fixed {P : E →L[ℂ] E} {v : E} (hv : P v = v) (z : ℂ) :
    selectivePhase P z v = z • v := by
  rw [selectivePhase_apply, hv]
  module

theorem selectivePhase_of_mem_ker {P : E →L[ℂ] E} {v : E} (hv : P v = 0) (z : ℂ) :
    selectivePhase P z v = v := by
  simp [selectivePhase_apply, hv]

/-- The target component is multiplied by `z`; only idempotence is needed. -/
theorem projection_selectivePhase {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (z : ℂ) (v : E) : P (selectivePhase P z v) = z • P v := by
  have hv : P (P v) = P v := congrArg (fun A : E →L[ℂ] E => A v) hP.eq
  simp only [selectivePhase_apply, map_add, map_smul, hv]
  module

/-- Composing two selective phases multiplies their scalar parameters. -/
theorem selectivePhase_mul {P : E →L[ℂ] E} (hP : IsIdempotentElem P) (z w : ℂ) :
    selectivePhase P z * selectivePhase P w = selectivePhase P (z * w) := by
  simp only [selectivePhase, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hP.eq]
  module

/-- The complementary component is unchanged. Self-adjointness is not needed here. -/
theorem complement_selectivePhase {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (z : ℂ) (v : E) : (1 - P) (selectivePhase P z v) = (1 - P) v := by
  have hv : P (P v) = P v := congrArg (fun A : E →L[ℂ] E => A v) hP.eq
  simp [selectivePhase_apply, map_add, map_smul, hv]

/-- Conjugate scalar parameters give a left inverse for idempotent targets.
Self-adjointness is required separately to identify this inverse with an adjoint. -/
theorem selectivePhase_star_mul {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    {z : ℂ} (hz : star z * z = 1) :
    selectivePhase P (star z) * selectivePhase P z = 1 := by
  rw [selectivePhase_mul hP, hz, selectivePhase_one]

theorem selectivePhase_mul_star {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    {z : ℂ} (hz : star z * z = 1) :
    selectivePhase P z * selectivePhase P (star z) = 1 := by
  rw [selectivePhase_mul hP, mul_comm z (star z), hz, selectivePhase_one]

/-- Only the measurement for this same `P` is asserted to be unchanged. -/
theorem successWeight_selectivePhase {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    {z : ℂ} (hz : ‖z‖ = 1) (v : E) :
    successWeight P (selectivePhase P z v) = successWeight P v := by
  unfold successWeight
  rw [projection_selectivePhase hP, norm_smul_of_norm_eq_one hz]

/-- The complementary component, and hence its weight, is unchanged for any `z`. -/
theorem failureWeight_selectivePhase {P : E →L[ℂ] E} (hP : IsIdempotentElem P)
    (z : ℂ) (v : E) :
    failureWeight P (selectivePhase P z v) = failureWeight P v := by
  unfold failureWeight
  rw [complement_selectivePhase hP]

namespace PureState

theorem selectivePhase_projection_self (s : PureState E) (z : ℂ) :
    selectivePhase s.projection z (s : E) = z • (s : E) :=
  selectivePhase_of_fixed s.projection_self z

theorem selectivePhase_projection_of_inner_eq_zero (s : PureState E) {v : E}
    (hv : inner ℂ (s : E) v = 0) (z : ℂ) : selectivePhase s.projection z v = v :=
  selectivePhase_of_mem_ker (s.projection_eq_zero_of_inner_eq_zero hv) z

end PureState

variable [CompleteSpace E]

/-- Taking the adjoint conjugates the scalar parameter. -/
theorem star_selectivePhase {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) (z : ℂ) :
    star (selectivePhase P z) = selectivePhase P (star z) := by
  simp only [selectivePhase, star_add, star_one, star_smul, star_sub, hP.star_eq]

/-- A selective phase on an orthogonal projection is unitary when `star z * z = 1`.
This scalar equation expresses unit modulus without introducing trigonometry. -/
theorem selectivePhase_mem_unitary {P : E →L[ℂ] E} (hP : IsStarProjection P)
    {z : ℂ} (hz : star z * z = 1) : selectivePhase P z ∈ unitary (E →L[ℂ] E) := by
  rw [Unitary.mem_iff, star_selectivePhase hP.isSelfAdjoint,
    selectivePhase_mul hP.isIdempotentElem, selectivePhase_mul hP.isIdempotentElem]
  rw [hz, mul_comm z (star z), hz]
  simp [selectivePhase]

/-- The overlap is linear in the real weights, explicitly embedded into `ℂ`.
The scalar `z` is arbitrary and the vector need not be normalized. -/
theorem inner_selectivePhase {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (z : ℂ) (v : E) :
    inner ℂ v (selectivePhase P z v) =
      (failureWeight P v : ℂ) + z * (successWeight P v : ℂ) := by
  rw [selectivePhase_apply_components, inner_add_right, inner_smul_right,
    inner_complement_eq_failureWeight hP, inner_projection_eq_successWeight hP]

/-- This failure-weight form specifically requires a normalized input. -/
theorem inner_selectivePhase_of_norm_eq_one {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (z : ℂ) {v : E} (hv : ‖v‖ = 1) :
    inner ℂ v (selectivePhase P z v) = z + (1 - z) * (failureWeight P v : ℂ) := by
  have hs := congrArg (fun r : ℝ => (r : ℂ))
    (successWeight_add_failureWeight_of_norm_eq_one hP hv)
  simp only [Complex.ofReal_add, Complex.ofReal_one] at hs
  rw [inner_selectivePhase hP]
  calc
    _ = z * ((successWeight P v : ℂ) + (failureWeight P v : ℂ)) +
        (1 - z) * (failureWeight P v : ℂ) := by ring
    _ = _ := by rw [hs, mul_one]

end
end QFixLean
