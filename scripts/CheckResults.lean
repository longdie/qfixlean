import QFixLean

/-!
Acceptance checks for existing public results, not new algorithm proofs.

The statements below fix the expected output, mathematical conclusion and
allowed hypotheses independently of the types inferred for the library lemmas.
Changing a lemma to require a formula, a nondegenerate input, or another
unproved premise must not silently turn the check into a weaker specification.
The axiom audit and public-import check are separate CI checks.

Run after `lake build --wfail`:
  lake env lean -DwarningAsError=true scripts/CheckResults.lean

Costs refer to the stated unoptimized constructions. The π/3 branch counts
target phases, whereas the selected algorithm counts bit-flip queries. Base
preparation and its adjoint have no target-query cost in these models.
-/

namespace QFixLean.ResultChecks

noncomputable section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- The initial unitary is supplied, and the same source/target persist at every level.
example (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    PiOverThree.searchRecursion U s hP 0 = U :=
  PiOverThree.searchRecursion_zero U s hP

example (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    (PiOverThree.searchRecursion U s hP (k + 1) : E →L[ℂ] E) =
      (PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) *
        phaseRotation s.projection (Real.pi / 3) *
        star (PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) *
        phaseRotation P (Real.pi / 3) *
        (PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) :=
  PiOverThree.coe_searchRecursion_succ U s hP k

-- Probabilities of the actual output, with natural exponents and no endpoint restriction.
example (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    failureWeight P ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E)) =
      failureWeight P ((U : E →L[ℂ] E) (s : E)) ^ ((3 : ℕ) ^ k) ∧
    successWeight P ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E)) =
      1 - failureWeight P ((U : E →L[ℂ] E) (s : E)) ^ ((3 : ℕ) ^ k) :=
  ⟨PiOverThree.searchRecursion_failureWeight U s hP k,
    PiOverThree.searchRecursion_successWeight U s hP k⟩

example (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    Antitone (fun k : ℕ =>
      failureWeight P ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E))) ∧
    Monotone (fun k : ℕ =>
      successWeight P ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E))) :=
  ⟨PiOverThree.searchRecursion_failureWeight_antitone U s hP,
    PiOverThree.searchRecursion_successWeight_monotone U s hP⟩

-- Only initial failure < 1 is added for convergence; failure = 0 is included.
example (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (hlt : failureWeight P ((U : E →L[ℂ] E) (s : E)) < 1) :
    Tendsto (fun k : ℕ =>
      failureWeight P ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E)))
      atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ =>
      successWeight P ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E)))
      atTop (𝓝 1) ∧
    Tendsto (fun k : ℕ =>
      ‖(1 - P) ((PiOverThree.searchRecursion U s hP k : E →L[ℂ] E) (s : E))‖)
      atTop (𝓝 0) :=
  ⟨PiOverThree.searchRecursion_failureWeight_tendsto_zero U s hP hlt,
    PiOverThree.searchRecursion_successWeight_tendsto_one U s hP hlt,
    PiOverThree.searchRecursion_complement_norm_tendsto_zero U s hP hlt⟩

-- Interpretation, counts and measured output all use the same expression C.
example (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    let C := PiOverThree.searchConstruction k
    let W := PiOverThree.Construction.interpret U s hP C
    W = PiOverThree.searchRecursion U s hP k ∧
    ‖(W : E →L[ℂ] E) (s : E)‖ = 1 ∧
    C.targetQueries = ((3 : ℕ) ^ k - 1) / 2 ∧
    C.baseCalls = (3 : ℕ) ^ k ∧ C.sourceCalls = C.targetQueries ∧
    failureWeight P ((W : E →L[ℂ] E) (s : E)) =
      failureWeight P ((U : E →L[ℂ] E) (s : E)) ^ (2 * C.targetQueries + 1) ∧
    successWeight P ((W : E →L[ℂ] E) (s : E)) =
      1 - failureWeight P ((U : E →L[ℂ] E) (s : E)) ^ (2 * C.targetQueries + 1) :=
  PiOverThree.searchConstruction_spec U s hP k

-- General scalar interfaces remain conditional; explicit-phase algorithms discharge them.
example (s : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    failureWeight P (FixedPoint.ExplicitPhases.p14Search s hP ℓ γ : E) =
      (Chebyshev.evalT (2 * ℓ + 1) (Real.sqrt (1 - successWeight P (s : E)) / γ) /
        Chebyshev.evalT (2 * ℓ + 1) (1 / γ)) ^ 2 ∧
    successWeight P (FixedPoint.ExplicitPhases.p14Search s hP ℓ γ : E) =
      1 - (Chebyshev.evalT (2 * ℓ + 1) (Real.sqrt (1 - successWeight P (s : E)) / γ) /
        Chebyshev.evalT (2 * ℓ + 1) (1 / γ)) ^ 2 :=
  FixedPoint.ExplicitPhases.p14Search_probabilities s hP ℓ hγ hγ1

-- Fix the rounding rule as part of the external parameter specification.
example (lam₀ δ : ℝ) :
    FixedPoint.Parameters.iterations lam₀ δ =
      ⌈(Real.log (2 / δ) / Real.sqrt lam₀) / 2⌉₊ ∧
    FixedPoint.Parameters.degree lam₀ δ =
      2 * FixedPoint.Parameters.iterations lam₀ δ + 1 :=
  ⟨rfl, rfl⟩

-- The actual compiled output includes A on the clean reference, not a supplied output state.
-- There is no formula, matching, reset or count premise, nor a rank/dimension restriction.
example (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) {lam₀ δ : ℝ}
    (hlam₀ : 0 < lam₀ ∧ lam₀ ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hinput : lam₀ ≤ successWeight P ((A : E →L[ℂ] E) (s₀ : E))) :
    let ℓ := FixedPoint.Parameters.iterations lam₀ δ
    let C := FixedPoint.QueryAlgorithm.selectedConstruction lam₀ δ
    let v := (FixedPoint.QueryConstruction.interpret A s₀ hP C :
      Ancilla.Space E →L[ℂ] Ancilla.Space E) (Ancilla.embed (s₀ : E))
    v = Ancilla.embed
      (FixedPoint.ExplicitPhases.parameterSearch (PureState.map A s₀) hP ℓ δ : E) ∧
    Ancilla.embed
      (FixedPoint.ExplicitPhases.p14ParameterSearch (PureState.map A s₀) hP ℓ δ : E) =
        ((-1 : ℂ) ^ ℓ) • v ∧
    ‖v‖ = 1 ∧ v.snd = 0 ∧
    failureWeight (Ancilla.lift P) v ≤ δ ^ 2 ∧
    1 - δ ^ 2 ≤ successWeight (Ancilla.lift P) v ∧
    C.queries = (2 * ℓ + 1) - 1 ∧
    (C.queries : ℝ) < Real.log (2 / δ) / Real.sqrt lam₀ + 2 ∧
    C.prepareCalls = ℓ + 1 ∧ C.unprepareCalls = ℓ ∧
    C.prepareCalls + C.unprepareCalls = 2 * ℓ + 1 ∧
    C.referencePhases = ℓ ∧ C.ancillaPhases = ℓ :=
  FixedPoint.QueryAlgorithm.selected_spec A s₀ hP hlam₀ hδ hδ1 hinput

end
end QFixLean.ResultChecks
