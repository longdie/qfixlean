module

public import QFixLean.Basic.State
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Orthogonal projection components

Targets use `IsStarProjection P`, with no rank restriction. Mathlib supplies
`hP.one_sub`, `hP.mul_one_sub_self` and `hP.one_sub_mul_self` for the complement
and the two zero operator products. Here we connect this algebra to vectors,
orthogonality, squared norms and complex inner products.

The rank-one source projection requires a normalized `PureState`. Components
remain general vectors, including zero; no component normalization is used.
-/

@[expose] public section

namespace QFixLean

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem projection_apply_self {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    P (P v) = P v :=
  congrArg (fun A : E →L[ℂ] E => A v) hP.isIdempotentElem.eq

@[simp]
theorem projection_complement_apply {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    P ((1 - P) v) = 0 := by
  simpa only [mul_apply_eq_comp, zero_apply] using
    congrArg (fun A : E →L[ℂ] E => A v) hP.mul_one_sub_self

@[simp]
theorem complement_projection_apply {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    (1 - P) (P v) = 0 := by
  simpa only [mul_apply_eq_comp, zero_apply] using
    congrArg (fun A : E →L[ℂ] E => A v) hP.one_sub_mul_self

omit [CompleteSpace E] in
/-- This algebraic decomposition holds even without the projection laws. -/
theorem projection_add_complement (P : E →L[ℂ] E) (v : E) :
    P v + (1 - P) v = v := by
  simp

/-- The target and complementary components are orthogonal. -/
theorem projection_inner_complement {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    inner ℂ (P v) ((1 - P) v) = 0 := by
  have hs : inner ℂ (P v) ((1 - P) v) = inner ℂ v (P ((1 - P) v)) :=
    hP.isSelfAdjoint.isSymmetric v ((1 - P) v)
  rw [hs, projection_complement_apply hP, inner_zero_right]

/-- Pythagoras for an arbitrary, possibly unnormalized input vector. -/
theorem projection_norm_sq_add {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    ‖P v‖ ^ 2 + ‖(1 - P) v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (P v) ((1 - P) v) (projection_inner_complement hP v)
  simpa only [projection_add_complement, ← pow_two] using h.symm

/-- The complex overlap with an orthogonal projection is its real squared norm. -/
theorem inner_projection_eq_norm_sq {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    inner ℂ v (P v) = ((‖P v‖ ^ 2 : ℝ) : ℂ) := by
  calc
    inner ℂ v (P v) = inner ℂ (P v) (P v) := by
      have hs : inner ℂ (P v) (P v) = inner ℂ v (P (P v)) :=
        hP.isSelfAdjoint.isSymmetric v (P v)
      rw [hs, projection_apply_self hP]
    _ = ((‖P v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rfl

theorem inner_complement_eq_norm_sq {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    inner ℂ v ((1 - P) v) = ((‖(1 - P) v‖ ^ 2 : ℝ) : ℂ) :=
  inner_projection_eq_norm_sq hP.one_sub v

namespace PureState

/-- The normalized source state's rank-one orthogonal projection. -/
def projection (s : PureState E) : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ (s : E) (s : E)

omit [CompleteSpace E] in
theorem projection_apply (s : PureState E) (v : E) :
    s.projection v = inner ℂ (s : E) v • (s : E) :=
  InnerProductSpace.rankOne_apply _ _ _

theorem isStarProjection_projection (s : PureState E) : IsStarProjection s.projection :=
  InnerProductSpace.isStarProjection_rankOne_self s.normalized

omit [CompleteSpace E] in
@[simp]
theorem projection_self (s : PureState E) : s.projection (s : E) = (s : E) := by
  rw [projection_apply, inner_self, one_smul]

omit [CompleteSpace E] in
theorem projection_eq_zero_of_inner_eq_zero (s : PureState E) {v : E}
    (h : inner ℂ (s : E) v = 0) : s.projection v = 0 := by
  rw [projection_apply, h, zero_smul]

end PureState
end
end QFixLean
