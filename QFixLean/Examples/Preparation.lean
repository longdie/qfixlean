module

public import QFixLean.FixedPoint.Preparation
public import QFixLean.Examples.Measurement
import Mathlib.Tactic.Ring

/-!
# An exact, nonidentity state preparation

The real rotation with columns `(3/5,4/5)` and `(-4/5,3/5)` is a native
unitary. Its inverse rotates in the opposite direction. The example tests the
source-phase implementation with a preparation different from identity.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

/-- The exact real rotation `[[3/5,-4/5],[4/5,3/5]]`. -/
def rationalPreparation : unitary (QubitSpace →L[ℂ] QubitSpace) :=
  Unitary.linearIsometryEquiv.symm
    { toFun v := WithLp.toLp 2 ![(3 / 5 : ℂ) * v 0 - (4 / 5 : ℂ) * v 1,
        (4 / 5 : ℂ) * v 0 + (3 / 5 : ℂ) * v 1]
      invFun v := WithLp.toLp 2 ![(3 / 5 : ℂ) * v 0 + (4 / 5 : ℂ) * v 1,
        -(4 / 5 : ℂ) * v 0 + (3 / 5 : ℂ) * v 1]
      left_inv v := by ext i; fin_cases i <;> simp <;> ring
      right_inv v := by ext i; fin_cases i <;> simp <;> ring
      map_add' v w := by ext i; fin_cases i <;> simp <;> ring
      map_smul' a v := by ext i; fin_cases i <;> simp <;> ring
      norm_map' v := by
        simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two]
        congr 1
        norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
          Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
        ring }

theorem rationalPreparation_apply (v : QubitSpace) :
    (rationalPreparation : QubitSpace →L[ℂ] QubitSpace) v =
      WithLp.toLp 2 ![(3 / 5 : ℂ) * v 0 - (4 / 5 : ℂ) * v 1,
        (4 / 5 : ℂ) * v 0 + (3 / 5 : ℂ) * v 1] := rfl

/-- The second column has the negative upper entry required by the rotation. -/
theorem rationalPreparation_basisOne :
    (rationalPreparation : QubitSpace →L[ℂ] QubitSpace) (basisOne : QubitSpace) =
      WithLp.toLp 2 ![(-4 / 5 : ℂ), (3 / 5 : ℂ)] := by
  ext i
  fin_cases i <;> norm_num [rationalPreparation_apply, basisOne]

@[simp] theorem rationalPreparation_basisZero :
    PureState.map rationalPreparation basisZero = rationalState := by
  apply PureState.ext
  ext i
  fin_cases i <;> norm_num [PureState.coe_map, rationalPreparation_apply, basisZero,
    rationalState]

/-- The adjoint rotates in the opposite direction, retaining both signs. -/
theorem rationalPreparation_star_apply (v : QubitSpace) :
    (star rationalPreparation : QubitSpace →L[ℂ] QubitSpace) v =
      WithLp.toLp 2 ![(3 / 5 : ℂ) * v 0 + (4 / 5 : ℂ) * v 1,
        -(4 / 5 : ℂ) * v 0 + (3 / 5 : ℂ) * v 1] := by
  let w : QubitSpace := WithLp.toLp 2 ![(3 / 5 : ℂ) * v 0 + (4 / 5 : ℂ) * v 1,
    -(4 / 5 : ℂ) * v 0 + (3 / 5 : ℂ) * v 1]
  have hw : (rationalPreparation : QubitSpace →L[ℂ] QubitSpace) w = v := by
    ext i
    fin_cases i <;> simp [rationalPreparation_apply, w] <;> ring
  change (star rationalPreparation : QubitSpace →L[ℂ] QubitSpace) v = w
  rw [← hw]
  exact congrArg (fun B : unitary (QubitSpace →L[ℂ] QubitSpace) =>
    (B : QubitSpace →L[ℂ] QubitSpace) w) (Unitary.star_mul_self rationalPreparation)

@[simp] theorem rationalPreparation_star_rationalState :
    PureState.map (star rationalPreparation) rationalState = basisZero := by
  rw [← rationalPreparation_basisZero, PureState.map_star_map]

theorem rationalPreparation_ne_one : rationalPreparation ≠ 1 := by
  intro h
  have hm := rationalPreparation_basisZero
  rw [h, PureState.map_one] at hm
  have hz := congrArg (fun s : PureState QubitSpace => (s : QubitSpace) 1) hm
  norm_num [basisZero, rationalState] at hz

/-- A concrete source-phase implementation by the nonidentity preparation. -/
theorem rationalState_sourcePhase_preparation (β : ℝ) :
    phaseRotation rationalState.projection β =
      (rationalPreparation : QubitSpace →L[ℂ] QubitSpace) *
        phaseRotation basisZero.projection β *
          star (rationalPreparation : QubitSpace →L[ℂ] QubitSpace) := by
  simpa using FixedPoint.Preparation.phaseRotation_map rationalPreparation basisZero β

end
end QFixLean.Examples
