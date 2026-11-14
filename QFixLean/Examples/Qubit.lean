module

public import QFixLean.Basic.Unitary
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact one-qubit states and a bit flip

The physical norm is the Euclidean norm on `EuclideanSpace ℂ (Fin 2)`.
The state `(3/5, 4/5)` and the Pauli X coordinate swap provide exact examples
of the normalized-state and native unitary interfaces.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

abbrev QubitSpace := EuclideanSpace ℂ (Fin 2)

/-- The computational basis state with amplitude one at index zero. -/
def basisZero : PureState QubitSpace :=
  ⟨WithLp.toLp 2 ![1, 0], by simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]⟩

/-- The computational basis state with amplitude one at index one. -/
def basisOne : PureState QubitSpace :=
  ⟨WithLp.toLp 2 ![0, 1], by simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]⟩

/-- A normalized state with two nonzero amplitudes, using exact rational constants. -/
def rationalState : PureState QubitSpace :=
  ⟨WithLp.toLp 2 ![3 / 5, 4 / 5], by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]⟩

theorem rationalState_amplitudes_ne_zero :
    (rationalState : QubitSpace) 0 ≠ 0 ∧ (rationalState : QubitSpace) 1 ≠ 0 := by
  norm_num [rationalState]

/-- Pauli X swaps the coordinates. The linear isometry equivalence supplies
the norm-preserving, invertible map from which Mathlib constructs a unitary. -/
def pauliX : unitary (QubitSpace →L[ℂ] QubitSpace) :=
  Unitary.linearIsometryEquiv.symm
    { toFun v := WithLp.toLp 2 ![v 1, v 0]
      invFun v := WithLp.toLp 2 ![v 1, v 0]
      left_inv v := by ext i; fin_cases i <;> rfl
      right_inv v := by ext i; fin_cases i <;> rfl
      map_add' v w := by ext i; fin_cases i <;> rfl
      map_smul' a v := by ext i; fin_cases i <;> rfl
      norm_map' v := by simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, add_comm] }

theorem pauliX_apply (v : QubitSpace) :
    (pauliX : QubitSpace →L[ℂ] QubitSpace) v = WithLp.toLp 2 ![v 1, v 0] := rfl

@[simp]
theorem pauliX_basisZero : PureState.map pauliX basisZero = basisOne := by
  apply PureState.ext
  rfl

@[simp]
theorem pauliX_basisOne : PureState.map pauliX basisOne = basisZero := by
  apply PureState.ext
  rfl

theorem pauliX_rationalState :
    (PureState.map pauliX rationalState : QubitSpace) = WithLp.toLp 2 ![4 / 5, 3 / 5] := rfl

/-- The same bit flip applied twice recovers any vector, including unnormalized ones. -/
theorem pauliX_self_inverse (v : QubitSpace) :
    (pauliX : QubitSpace →L[ℂ] QubitSpace) ((pauliX : QubitSpace →L[ℂ] QubitSpace) v) = v := by
  ext i
  fin_cases i <;> rfl

@[simp]
theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  exact pauliX_self_inverse

@[simp]
theorem pauliX_inv : pauliX⁻¹ = pauliX := inv_eq_of_mul_eq_one_left pauliX_mul_self

@[simp]
theorem pauliX_star : star pauliX = pauliX := pauliX_inv

theorem pauliX_ne_one : pauliX ≠ 1 := by
  intro h
  have hz := congrArg (fun U : unitary (QubitSpace →L[ℂ] QubitSpace) =>
    ((U : QubitSpace →L[ℂ] QubitSpace) (basisZero : QubitSpace)) 0) h
  norm_num [pauliX_apply, basisZero] at hz

theorem pauliX_map_twice (ψ : PureState QubitSpace) :
    PureState.map pauliX (PureState.map pauliX ψ) = ψ := by
  rw [← PureState.map_mul, pauliX_mul_self, PureState.map_one]

end
end QFixLean.Examples
