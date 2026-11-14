module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Module

/-!
# Selective phase operators

The main representation is `E →L[ℂ] E`. Multiplication acts right to left;
`star` is the adjoint. Orthogonal projections use Mathlib's mathematical
predicate `IsStarProjection`, with no restriction on their rank.

`selectivePhase P z = 1 + (z - 1) • P` multiplies the range of `P` by `z`.
The scalar parameter separates the operator algebra from the future angular
interface `z = exp (I * φ)`. Unitarity requires a unit-modulus scalar.
-/

@[expose] public section

namespace QFixLean

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Selective multiplication by `z` on the range of a projection `P`. -/
def selectivePhase (P : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E := 1 + (z - 1) • P

theorem selectivePhase_apply (P : E →L[ℂ] E) (z : ℂ) (v : E) :
    selectivePhase P z v = v + (z - 1) • P v := rfl

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

end
end QFixLean
