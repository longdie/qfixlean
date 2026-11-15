module

public import QFixLean.Basic.PhaseRotation
import Mathlib.Tactic.Ring

/-!
# The π/3 search step

Reference: Grover, *A different kind of quantum search*, quant-ph/0503205v1,
Section 2, equation (1): the operator product `U R_s U† R_t U`;
Section 3: its amplitude expansion.
The proofs below are written independently using Mathlib's operator interfaces.

The symbolic expansion is connected to the actual normalized output of
`searchStep`. Its complementary vector is `ζ ε` times the input complement,
so its failure probability is exactly `ε³`. Targets are arbitrary orthogonal
projections; this gives an explicit projector formulation of the paper's
state/subspace setting. Recursive correctness is developed in `Recursion.lean`,
with endpoints in `Boundary.lean` and probability/complement-norm convergence
in `Convergence.lean`. `Resources.lean` connects this recursion to a counted
construction under an explicit target-phase query model.
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

/-- The normalized-output bridge for a scalar satisfying the π/3 relation.
No target-rank or nonzero-component assumptions are needed. -/
theorem step_failure_vector_of_phase_relation (U : unitary (E →L[ℂ] E))
    (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (z : ℂ) (hz : (z - 1) ^ 2 = -z) :
    (1 - P) (step (U : E →L[ℂ] E) P (s : E) z (s : E)) =
      (z * (failureWeight P ((U : E →L[ℂ] E) (s : E)) : ℂ)) •
        (1 - P) ((U : E →L[ℂ] E) (s : E)) := by
  rw [step_failure_expansion U (s : E) hP.isIdempotentElem,
    inner_selectivePhase_of_norm_eq_one hP z ((Unitary.norm_map U _).trans s.normalized),
    piOverThree_coefficient z _ hz]

/-- P05 v1, Section 2, equation (1), with both angles equal to positive π/3.
This native unitary is the five-factor operator, rather than a probability model. -/
def searchStep (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : unitary (E →L[ℂ] E) :=
  U * phaseRotationUnitary s.isStarProjection_projection (Real.pi / 3) * star U *
    phaseRotationUnitary hP (Real.pi / 3) * U

/-- The bundled construction has exactly the original symbolic operator semantics. -/
@[simp]
theorem coe_searchStep (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    (searchStep U s hP : E →L[ℂ] E) =
      step (U : E →L[ℂ] E) P (s : E) (phaseFactor (Real.pi / 3)) := rfl

theorem step_piOverThree_mem_unitary (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    step (U : E →L[ℂ] E) P (s : E) (phaseFactor (Real.pi / 3)) ∈
      unitary (E →L[ℂ] E) :=
  (searchStep U s hP).property

/-- The actual output is normalized, so its weights are measurement probabilities. -/
theorem searchStep_normalized (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    ‖(searchStep U s hP : E →L[ℂ] E) (s : E)‖ = 1 :=
  (Unitary.norm_map (searchStep U s hP) _).trans s.normalized

/-- Exact failure vector for the exponential π/3 phase. This is the projector
form of the complementary amplitude calculation in P05 v1, Section 3. -/
theorem searchStep_failure_vector (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    (1 - P) ((searchStep U s hP : E →L[ℂ] E) (s : E)) =
      (phaseFactor (Real.pi / 3) *
        (failureWeight P ((U : E →L[ℂ] E) (s : E)) : ℂ)) •
          (1 - P) ((U : E →L[ℂ] E) (s : E)) := by
  rw [coe_searchStep]
  exact step_failure_vector_of_phase_relation U s hP _ phaseFactor_pi_div_three_sub_one_sq

/-- P05 v1, Section 3: the actual output failure probability is the cube of
the input failure probability, including the endpoints zero and one. -/
theorem searchStep_failureWeight (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    failureWeight P ((searchStep U s hP : E →L[ℂ] E) (s : E)) =
      (failureWeight P ((U : E →L[ℂ] E) (s : E))) ^ 3 := by
  let ε := failureWeight P ((U : E →L[ℂ] E) (s : E))
  have hε : 0 ≤ ε := failureWeight_nonneg P _
  change ‖(1 - P) ((searchStep U s hP : E →L[ℂ] E) (s : E))‖ ^ 2 = ε ^ 3
  rw [searchStep_failure_vector, norm_smul, norm_mul, phaseFactor_norm,
    one_mul, Complex.norm_of_nonneg hε, mul_pow]
  change ε ^ 2 * ε = ε ^ 3
  ring

/-- The success guarantee for that same normalized output, P05 v1, Section 3. -/
theorem searchStep_successWeight (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    successWeight P ((searchStep U s hP : E →L[ℂ] E) (s : E)) =
      1 - (failureWeight P ((U : E →L[ℂ] E) (s : E))) ^ 3 := by
  have h := successWeight_add_failureWeight_of_norm_eq_one hP (searchStep_normalized U s hP)
  rw [searchStep_failureWeight] at h
  exact (eq_sub_iff_add_eq).2 h

end
end QFixLean.PiOverThree
