module

public import QFixLean.Basic.PhaseRotation

/-!
# Source phases from a fixed state preparation

For a reference state `s₀` and its unitary preparation `A`, source phases about
`A s₀` are implemented in time order by `A†`, a reference phase, and `A`.
The identities are exact operator identities, with no discarded global phase.
-/

@[expose] public section

namespace QFixLean.FixedPoint.Preparation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Preparing a state conjugates its rank-one projection. -/
theorem projection_map (A : unitary (E →L[ℂ] E)) (s₀ : PureState E) :
    (PureState.map A s₀).projection =
      (A : E →L[ℂ] E) * s₀.projection * star (A : E →L[ℂ] E) := by
  ext v
  simp only [PureState.projection_apply, PureState.coe_map, mul_apply_eq_comp, map_smul]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- The source phase uses the same fixed preparation and reference state. -/
theorem phaseRotation_map (A : unitary (E →L[ℂ] E)) (s₀ : PureState E) (β : ℝ) :
    phaseRotation (PureState.map A s₀).projection β =
      (A : E →L[ℂ] E) * phaseRotation s₀.projection β * star (A : E →L[ℂ] E) := by
  rw [projection_map]
  simp only [phaseRotation, selectivePhase, mul_add, add_mul, mul_one,
    mul_smul_comm, smul_mul_assoc, mul_assoc]
  have hA : (A : E →L[ℂ] E) * star (A : E →L[ℂ] E) = 1 :=
    congrArg Subtype.val (Unitary.mul_star_self A)
  rw [hA]

/-- The native unitary version of the exact source-phase implementation. -/
theorem phaseRotationUnitary_map (A : unitary (E →L[ℂ] E)) (s₀ : PureState E) (β : ℝ) :
    phaseRotationUnitary (PureState.map A s₀).isStarProjection_projection β =
      A * phaseRotationUnitary s₀.isStarProjection_projection β * star A := by
  apply Subtype.ext
  exact phaseRotation_map A s₀ β

end
end QFixLean.FixedPoint.Preparation
