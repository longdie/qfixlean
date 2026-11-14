module

public import QFixLean.Basic.Probability
public import QFixLean.Examples.Qubit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact projective measurement examples

The target `firstBasisTarget` retains the first qubit coordinate. The existing
state `(3/5, 4/5)` has exact success and failure probabilities `9/25` and `16/25`.
A three-dimensional target retaining two coordinates also illustrates that the
general interface has no rank-one restriction. All states and values are exact.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

/-- The target subspace spanned by the first computational basis state. -/
def firstBasisTarget : QubitSpace →L[ℂ] QubitSpace := basisZero.projection

theorem firstBasisTarget_isStarProjection : IsStarProjection firstBasisTarget :=
  basisZero.isStarProjection_projection

theorem firstBasisTarget_apply (v : QubitSpace) :
    firstBasisTarget v = WithLp.toLp 2 ![v 0, 0] := by
  ext i
  fin_cases i <;> simp [firstBasisTarget, PureState.projection_apply, basisZero,
    PiLp.inner_apply, Fin.sum_univ_two]

@[simp]
theorem firstBasisTarget_basisZero :
    firstBasisTarget (basisZero : QubitSpace) = (basisZero : QubitSpace) :=
  basisZero.projection_self

@[simp]
theorem firstBasisTarget_basisOne : firstBasisTarget (basisOne : QubitSpace) = 0 := by
  apply basisZero.projection_eq_zero_of_inner_eq_zero
  simp [basisZero, basisOne, PiLp.inner_apply, Fin.sum_univ_two]

theorem rationalState_success :
    successWeight firstBasisTarget (rationalState : QubitSpace) = (9 / 25 : ℝ) := by
  norm_num [successWeight, firstBasisTarget_apply, rationalState,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

theorem rationalState_failure :
    failureWeight firstBasisTarget (rationalState : QubitSpace) = (16 / 25 : ℝ) := by
  norm_num [failureWeight, sub_apply, firstBasisTarget_apply, rationalState,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

abbrev ThreeLevelSpace := EuclideanSpace ℂ (Fin 3)

/-- A normalized vector along the third coordinate. -/
def thirdBasis : PureState ThreeLevelSpace :=
  ⟨WithLp.toLp 2 ![0, 0, 1], by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩

/-- The target retaining both the first and second coordinates. -/
def firstTwoTarget : ThreeLevelSpace →L[ℂ] ThreeLevelSpace :=
  1 - thirdBasis.projection

theorem firstTwoTarget_isStarProjection : IsStarProjection firstTwoTarget :=
  thirdBasis.isStarProjection_projection.one_sub

theorem firstTwoTarget_apply (v : ThreeLevelSpace) :
    firstTwoTarget v = WithLp.toLp 2 ![v 0, v 1, 0] := by
  ext i
  fin_cases i <;> simp [firstTwoTarget, PureState.projection_apply, thirdBasis,
    PiLp.inner_apply, Fin.sum_univ_three]

/-- An exact normalized input with nonzero target and complementary components. -/
def threeLevelState : PureState ThreeLevelSpace :=
  ⟨WithLp.toLp 2 ![1 / 3, 2 / 3, 2 / 3], by
    norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩

theorem threeLevelState_success :
    successWeight firstTwoTarget (threeLevelState : ThreeLevelSpace) = (5 / 9 : ℝ) := by
  norm_num [successWeight, firstTwoTarget_apply, threeLevelState,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

theorem threeLevelState_failure :
    failureWeight firstTwoTarget (threeLevelState : ThreeLevelSpace) = (4 / 9 : ℝ) := by
  norm_num [failureWeight, sub_apply, firstTwoTarget_apply, threeLevelState,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

end
end QFixLean.Examples
