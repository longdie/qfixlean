module

public import QFixLean.Basic.Phase
import Mathlib.Tactic.Ring

/-!
# Symbolic single-step expansion

Reference: Grover, *A different kind of quantum search*, quant-ph/0503205v1,
Section 2, equation (1): the operator product `U R_s U† R_t U`;
Section 3: its amplitude expansion.
The proofs below are written independently using Mathlib's operator interfaces.

This is the algebraic part of the planned π/3 proof. The overlap in
`step_failure_expansion` has not yet been identified with a failure probability.
The specialization `z = exp (I * π / 3)`, normalization/probability bridge,
and failure-probability-cubing theorem remain to be proved.
-/

@[expose] public section

namespace QFixLean.PiOverThree

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A symbolic search step. The source rank-one map is an orthogonal projection
when `‖s‖ = 1`; the definition itself does not assert normalization or unitarity. -/
def step (U P : E →L[ℂ] E) (s : E) (z : ℂ) : E →L[ℂ] E :=
  U * selectivePhase (InnerProductSpace.rankOne ℂ s s) z * star U *
    selectivePhase P z * U

/-- Conjugation transports a rank-one map to the image of its vector. -/
theorem conjugate_rankOne (U : E →L[ℂ] E) (s : E) :
    U * InnerProductSpace.rankOne ℂ s s * star U =
      InnerProductSpace.rankOne ℂ (U s) (U s) := by
  simp [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
    InnerProductSpace.rankOne_comp, ContinuousLinearMap.star_eq_adjoint]

/-- Unitary conjugation transports the source selective phase. -/
theorem conjugate_sourcePhase (U : unitary (E →L[ℂ] E)) (s : E) (z : ℂ) :
    (U : E →L[ℂ] E) * selectivePhase (InnerProductSpace.rankOne ℂ s s) z *
      star (U : E →L[ℂ] E) =
      selectivePhase (InnerProductSpace.rankOne ℂ
        ((U : E →L[ℂ] E) s) ((U : E →L[ℂ] E) s)) z := by
  simp only [selectivePhase, mul_add, mul_one, add_mul, mul_smul_comm,
    smul_mul_assoc, Unitary.mul_star_self_of_mem U.property, conjugate_rankOne]

/-- Exact complementary output of the symbolic step, expressed using an overlap.
Only idempotence is needed for `P`; no one-dimensional target assumption is used.
For a nonorthogonal idempotent this is an algebraic complement, not a measurement. -/
theorem step_failure_expansion (U : unitary (E →L[ℂ] E)) (s : E)
    {P : E →L[ℂ] E} (hP : IsIdempotentElem P) (z : ℂ) :
    (1 - P) (step (U : E →L[ℂ] E) P s z s) =
      (1 + (z - 1) * inner ℂ ((U : E →L[ℂ] E) s)
        (selectivePhase P z ((U : E →L[ℂ] E) s))) • (1 - P) ((U : E →L[ℂ] E) s) := by
  unfold step
  rw [conjugate_sourcePhase]
  simp only [mul_apply_eq_comp]
  rw [selectivePhase_apply]
  simp only [InnerProductSpace.rankOne_apply, map_add, map_smul, smul_smul]
  rw [complement_selectivePhase hP]
  rw [add_smul, one_smul]

/-- The scalar cancellation needed at π/3. Here `e` is an arbitrary complex
scalar; identifying it with the real failure probability is a separate task. -/
theorem piOverThree_coefficient (z e : ℂ) (hz : (z - 1) ^ 2 = -z) :
    1 + (z - 1) * (z + (1 - z) * e) = z * e := by
  calc
    _ = (1 - e) * ((z - 1) ^ 2 + z) + z * e := by ring
    _ = _ := by rw [hz]; ring

end
end QFixLean.PiOverThree
