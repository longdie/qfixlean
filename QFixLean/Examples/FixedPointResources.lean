module

public import QFixLean.FixedPoint.Resources
public import QFixLean.Examples.Preparation

/-!
# Exact bit-oracle costs and the selected algorithm

Small counts reduce the actual syntax rather than instantiating a cost formula.
The joint example starts with a nonidentity preparation and uses the symbolic
selection `λ₀=1/4, δ=1/2`, whose odd degree is exactly five.
-/

@[expose] public section

namespace QFixLean.Examples

open FixedPoint FixedPoint.QueryConstruction FixedPoint.QueryAlgorithm

noncomputable section

/-- Direct traversal of the zero-, one- and two-step expressions. -/
theorem explicit_small_query_counts (γ : ℝ) :
    (searchConstruction 0 γ).queries = 0 ∧
    (searchConstruction 1 γ).queries = 2 ∧
    (searchConstruction 2 γ).queries = 4 := ⟨rfl, rfl, rfl⟩

/-- Direct traversal includes the initial preparation, once and only once. -/
theorem explicit_small_preparation_counts (γ : ℝ) :
    (construction 0 γ).prepareCalls = 1 ∧ (construction 0 γ).unprepareCalls = 0 ∧
    (construction 1 γ).prepareCalls = 2 ∧ (construction 1 γ).unprepareCalls = 1 ∧
    (construction 2 γ).prepareCalls = 3 ∧ (construction 2 γ).unprepareCalls = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The full two-step syntax: step one acts before step two, then read from right
for the preparation within every source phase. All angles remain exact. -/
theorem explicit_two_construction (γ : ℝ) :
    construction 2 γ =
      ((.skip *
        ((.gate .prepare * .gate (.referencePhase (ExplicitPhases.pair 2 γ 2).2) *
          .gate .unprepare) *
         (.gate .oracle * .gate (.ancillaPhase (ExplicitPhases.pair 2 γ 2).1) *
          .gate .oracle))) *
        ((.gate .prepare * .gate (.referencePhase (ExplicitPhases.pair 2 γ 1).2) *
          .gate .unprepare) *
         (.gate .oracle * .gate (.ancillaPhase (ExplicitPhases.pair 2 γ 1).1) *
          .gate .oracle))) * .gate .prepare := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Zero search steps still execute the initial, possibly nonidentity, A. -/
theorem complete_zero_run (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (γ : ℝ) :
    run A s₀ hP 0 γ = Ancilla.embed (PureState.map A s₀ : E) := by
  rw [run_eq_embed, ExplicitPhases.search_zero]

/-- The same fixed prepared source is used in both actual iterates. -/
theorem complete_two_run (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (γ : ℝ) :
    run A s₀ hP 2 γ = Ancilla.embed
      ((iterate (PureState.map A s₀) hP (ExplicitPhases.pair 2 γ 2).1
        (ExplicitPhases.pair 2 γ 2).2 : E →L[ℂ] E)
        ((iterate (PureState.map A s₀) hP (ExplicitPhases.pair 2 γ 1).1
          (ExplicitPhases.pair 2 γ 1).2 : E →L[ℂ] E) (PureState.map A s₀ : E))) := by
  rw [run_eq_embed]
  rfl

/-- A single P24 step has the opposite exact P14 sign; two steps have the same sign. -/
theorem small_p14_phases (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (γ : ℝ) :
    Ancilla.embed (ExplicitPhases.p14Search (PureState.map A s₀) hP 1 γ : E) =
      -run A s₀ hP 1 γ ∧
    Ancilla.embed (ExplicitPhases.p14Search (PureState.map A s₀) hP 2 γ : E) =
      run A s₀ hP 2 γ := by
  constructor
  · simpa using p14_embed_eq_phase_run A s₀ hP 1 γ
  · simpa using p14_embed_eq_phase_run A s₀ hP 2 γ

/-- Complete nonidentity example: actual output, clean ancilla, M17 data state,
error bound and occurrence counts all concern the very same selected circuit. -/
theorem rational_selected_spec :
    let C := selectedConstruction (1 / 4) (1 / 2)
    let v := selectedRun rationalPreparation basisZero firstBasisTarget_isStarProjection
      (1 / 4) (1 / 2)
    v = Ancilla.embed (ExplicitPhases.parameterSearch rationalState
      firstBasisTarget_isStarProjection 2 (1 / 2) : QubitSpace) ∧
    v = Ancilla.embed (ExplicitPhases.p14ParameterSearch rationalState
      firstBasisTarget_isStarProjection 2 (1 / 2) : QubitSpace) ∧
    ‖v‖ = 1 ∧ v.snd = 0 ∧
    failureWeight (Ancilla.lift firstBasisTarget) v ≤ (1 / 4 : ℝ) ∧
    (3 / 4 : ℝ) ≤ successWeight (Ancilla.lift firstBasisTarget) v ∧
    C.queries = 4 ∧ C.prepareCalls = 3 ∧ C.unprepareCalls = 2 ∧
    C.referencePhases = 2 ∧ C.ancillaPhases = 2 := by
  have hinput : (1 / 4 : ℝ) ≤
      successWeight firstBasisTarget (PureState.map rationalPreparation basisZero : QubitSpace) := by
    rw [rationalPreparation_basisZero, rationalState_success]
    norm_num
  have h := selected_spec rationalPreparation basisZero firstBasisTarget_isStarProjection
    (by norm_num : (1 / 4 : ℝ) ∈ Set.Ioc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hinput
  dsimp only at h ⊢
  rw [Parameters.iterations_quarter_half, Parameters.degree_quarter_half,
    rationalPreparation_basisZero] at h
  norm_num at h
  rcases h with ⟨hv, hp14, hn, hclean, hf, hs, hq, _, hA, hAd, _, hr, ha⟩
  exact ⟨hv, hp14.symm, hn, hclean, hf, hs, hq, hA, hAd, hr, ha⟩

/-- A unit lower-bound promise is accepted by the selected algorithm. -/
theorem fully_good_selected (δ : ℝ) :
    let v := selectedRun (1 : unitary (QubitSpace →L[ℂ] QubitSpace)) basisZero
      firstBasisTarget_isStarProjection 1 δ
    v.snd = 0 ∧ successWeight (Ancilla.lift firstBasisTarget) v = 1 ∧
      failureWeight (Ancilla.lift firstBasisTarget) v = 0 := by
  dsimp only
  rw [selectedRun_eq_embed]
  simp only [PureState.map_one, Ancilla.embed_snd, Ancilla.successWeight_embed,
    Ancilla.failureWeight_embed, true_and]
  apply ExplicitPhases.search_probabilities_of_success_one
  simp [successWeight]

/-- A zero-success input is still a valid compiled execution, even though it
cannot satisfy a positive success-lower-bound promise. -/
theorem fully_bad_compiled (ℓ : ℕ) (γ : ℝ) :
    let v := run (1 : unitary (QubitSpace →L[ℂ] QubitSpace)) basisOne
      firstBasisTarget_isStarProjection ℓ γ
    v.snd = 0 ∧ successWeight (Ancilla.lift firstBasisTarget) v = 0 ∧
      failureWeight (Ancilla.lift firstBasisTarget) v = 1 := by
  dsimp only
  rw [run_eq_embed]
  simp only [PureState.map_one, Ancilla.embed_snd, Ancilla.successWeight_embed,
    Ancilla.failureWeight_embed, true_and]
  apply ExplicitPhases.search_probabilities_of_success_zero
  simp [successWeight]

/-- A target retaining two coordinates uses the same oracle compiler and counts. -/
theorem rank_two_compiled (ℓ : ℕ) (γ : ℝ) :
    run (1 : unitary (ThreeLevelSpace →L[ℂ] ThreeLevelSpace)) threeLevelState
      firstTwoTarget_isStarProjection ℓ γ =
      Ancilla.embed (ExplicitPhases.search threeLevelState firstTwoTarget_isStarProjection
        ℓ γ : ThreeLevelSpace) ∧ (construction ℓ γ).queries = 2 * ℓ := by
  constructor
  · simpa using (run_eq_embed (1 : unitary (ThreeLevelSpace →L[ℂ] ThreeLevelSpace))
      threeLevelState firstTwoTarget_isStarProjection ℓ γ)
  · exact (construction_counts ℓ γ).1

end
end QFixLean.Examples
