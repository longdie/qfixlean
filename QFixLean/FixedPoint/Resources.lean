module

public import QFixLean.FixedPoint.Compilation
public import QFixLean.FixedPoint.Correctness
public import QFixLean.FixedPoint.Parameters

/-!
# A selected fixed-point algorithm with actual bit-oracle costs

P14 v2, Figure 2, equations (1), (3), and `L-1=2ℓ`. The same expression is
interpreted as an ancilla-space unitary and traversed for all resource counts.
The basic query bound assumes that the supplied preparation and its inverse
have no target-oracle cost. Reference and ancilla phases are supplied exact
operations, without a finite-precision synthesis or optimality claim.
-/

@[expose] public section

namespace QFixLean.FixedPoint.QueryAlgorithm

open QueryConstruction

noncomputable section

/-- Search with its prepared input already supplied. -/
def searchConstruction (ℓ : ℕ) (γ : ℝ) : QueryConstruction :=
  compile (ExplicitPhases.schedule ℓ γ)

/-- The full construction includes one initial preparation of its reference. -/
def construction (ℓ : ℕ) (γ : ℝ) : QueryConstruction :=
  complete (ExplicitPhases.schedule ℓ γ)

/-- Explicitly selected construction depending only on the promise and tolerance. -/
def selectedConstruction (lam₀ δ : ℝ) : QueryConstruction :=
  construction (Parameters.iterations lam₀ δ)
    (Chebyshev.parameter (Parameters.degree lam₀ δ) δ)

/-- General search counts derived by traversing its actual primitive expression. -/
theorem search_counts (ℓ : ℕ) (γ : ℝ) :
    (searchConstruction ℓ γ).queries = 2 * ℓ ∧
    (searchConstruction ℓ γ).prepareCalls = ℓ ∧
    (searchConstruction ℓ γ).unprepareCalls = ℓ ∧
    (searchConstruction ℓ γ).referencePhases = ℓ ∧
    (searchConstruction ℓ γ).ancillaPhases = ℓ := by
  simpa only [searchConstruction, ExplicitPhases.schedule_length] using compile_counts (ExplicitPhases.schedule ℓ γ)

/-- Include the initial A, keeping its inverse and the query oracle distinct. -/
theorem construction_counts (ℓ : ℕ) (γ : ℝ) :
    (construction ℓ γ).queries = 2 * ℓ ∧
    (construction ℓ γ).prepareCalls = ℓ + 1 ∧
    (construction ℓ γ).unprepareCalls = ℓ ∧
    (construction ℓ γ).referencePhases = ℓ ∧
    (construction ℓ γ).ancillaPhases = ℓ := by
  simpa only [construction, ExplicitPhases.schedule_length] using complete_counts (ExplicitPhases.schedule ℓ γ)

theorem construction_preparation_total (ℓ : ℕ) (γ : ℝ) :
    (construction ℓ γ).prepareCalls + (construction ℓ γ).unprepareCalls = 2 * ℓ + 1 := by
  have hc := construction_counts ℓ γ
  omega

/-- Identify the expression's query count with the selected scalar count. -/
theorem selected_queries (lam₀ δ : ℝ) :
    (selectedConstruction lam₀ δ).queries = Parameters.queries lam₀ δ :=
  (construction_counts _ _).1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The output vector of the actual full circuit on the clean reference input. -/
def run (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) : Ancilla.Space E :=
  (interpret A s₀ hP (construction ℓ γ) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
    (Ancilla.embed (s₀ : E))

/-- The chosen actual circuit, including preparation and the same reused ancilla. -/
def selectedRun (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (lam₀ δ : ℝ) : Ancilla.Space E :=
  (interpret A s₀ hP (selectedConstruction lam₀ δ) :
    Ancilla.Space E →L[ℂ] Ancilla.Space E) (Ancilla.embed (s₀ : E))

/-- No probability equality is assumed: the actual clean vector is identified. -/
theorem run_eq_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    run A s₀ hP ℓ γ =
      Ancilla.embed (ExplicitPhases.search (PureState.map A s₀) hP ℓ γ : E) :=
  interpret_complete_embed A s₀ hP _

/-- If the prepared state is supplied, the search block gives the same output. -/
theorem searchConstruction_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    (interpret A s₀ hP (searchConstruction ℓ γ) :
      Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed (PureState.map A s₀ : E)) = run A s₀ hP ℓ γ := by
  rw [run_eq_embed]
  exact interpret_compile_embed A s₀ hP _ _

/-- The P14 sign is retained as an equality of vectors in the extended space. -/
theorem p14_embed_eq_phase_run (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    Ancilla.embed (ExplicitPhases.p14Search (PureState.map A s₀) hP ℓ γ : E) =
      ((-1 : ℂ) ^ ℓ) • run A s₀ hP ℓ γ := by
  rw [ExplicitPhases.p14Search_eq_phase, Ancilla.embed_smul, run_eq_embed]

theorem run_normalized (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    ‖run A s₀ hP ℓ γ‖ = 1 := by
  rw [run_eq_embed, Ancilla.norm_embed]
  exact (ExplicitPhases.search _ hP ℓ γ).normalized

/-- The same output has a clean ancilla, with no input success restriction. -/
theorem run_clean (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    (run A s₀ hP ℓ γ).snd = 0 := by rw [run_eq_embed, Ancilla.embed_snd]

/-- Both lifted probabilities equal the same actual M17 data probabilities. -/
theorem run_weights (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    failureWeight (Ancilla.lift P) (run A s₀ hP ℓ γ) =
      failureWeight P (ExplicitPhases.search (PureState.map A s₀) hP ℓ γ : E) ∧
    successWeight (Ancilla.lift P) (run A s₀ hP ℓ γ) =
      successWeight P (ExplicitPhases.search (PureState.map A s₀) hP ℓ γ : E) := by
  rw [run_eq_embed]
  exact ⟨Ancilla.failureWeight_embed _ _, Ancilla.successWeight_embed _ _⟩

theorem selectedRun_eq_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (lam₀ δ : ℝ) :
    selectedRun A s₀ hP lam₀ δ =
      Ancilla.embed (ExplicitPhases.parameterSearch (PureState.map A s₀) hP
        (Parameters.iterations lam₀ δ) δ : E) :=
  run_eq_embed A s₀ hP _ _

/-- Complete selected algorithm: no formula, phase-correctness, reset, count,
matching, or sufficiently-large-degree premise is supplied by the caller.
The normalized output and its measured weights belong to the counted circuit.
The target may have arbitrary rank; only its initial success is promised. -/
theorem selected_spec (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) {lam₀ δ : ℝ}
    (hlam₀ : lam₀ ∈ Set.Ioc (0 : ℝ) 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hinput : lam₀ ≤ successWeight P (PureState.map A s₀ : E)) :
    let ℓ := Parameters.iterations lam₀ δ
    let L := Parameters.degree lam₀ δ
    let C := selectedConstruction lam₀ δ
    let v := selectedRun A s₀ hP lam₀ δ
    v = Ancilla.embed (ExplicitPhases.parameterSearch (PureState.map A s₀) hP ℓ δ : E) ∧
    Ancilla.embed (ExplicitPhases.p14ParameterSearch (PureState.map A s₀) hP ℓ δ : E) =
      ((-1 : ℂ) ^ ℓ) • v ∧
    ‖v‖ = 1 ∧ v.snd = 0 ∧
    failureWeight (Ancilla.lift P) v ≤ δ ^ 2 ∧
    1 - δ ^ 2 ≤ successWeight (Ancilla.lift P) v ∧
    C.queries = L - 1 ∧
    (C.queries : ℝ) < Parameters.bound lam₀ δ + 2 ∧
    C.prepareCalls = ℓ + 1 ∧ C.unprepareCalls = ℓ ∧
    C.prepareCalls + C.unprepareCalls = L ∧
    C.referencePhases = ℓ ∧ C.ancillaPhases = ℓ := by
  dsimp only
  have he := selectedRun_eq_embed A s₀ hP lam₀ δ
  have herror := ExplicitPhases.uniform_error_guarantee (PureState.map A s₀) hP
    (Parameters.iterations lam₀ δ) hδ hδ1 hlam₀
    (Parameters.parameter_match hlam₀.1 hδ hδ1) hinput
  have hc := construction_counts (Parameters.iterations lam₀ δ)
    (Chebyshev.parameter (Parameters.degree lam₀ δ) δ)
  refine ⟨he, p14_embed_eq_phase_run A s₀ hP _ _, run_normalized A s₀ hP _ _,
    run_clean A s₀ hP _ _, ?_, ?_, ?_, ?_, hc.2.1, hc.2.2.1,
    construction_preparation_total _ _, hc.2.2.2.1, hc.2.2.2.2⟩
  · rw [he, Ancilla.failureWeight_embed]
    exact herror.1
  · rw [he, Ancilla.successWeight_embed]
    exact herror.2
  · rw [selected_queries, Parameters.queries_eq_degree_sub_one]
  · rw [selected_queries]
    exact Parameters.queries_lt_bound_add_two hlam₀.1 hδ hδ1

end
end QFixLean.FixedPoint.QueryAlgorithm
