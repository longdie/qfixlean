module

public import QFixLean.PiOverThree.Construction
public import QFixLean.PiOverThree.Recursion
import Lean.Elab.Tactic.Omega

/-!
# Resources of the actual recursive π/3 construction

Reference: Grover, *A different kind of quantum search*, quant-ph/0503205v1,
Section 4, equations (3), (4) and the following query/probability formula.

`searchConstruction` records the unoptimized expression, including inverse
subconstructions. Its interpretation is exactly `searchRecursion`, retaining
global phase. Target phases and their inverses each cost one target-phase query;
base `U`/`U†` calls and source phases are counted separately. The model assumes
the base primitive has no target-query cost and the source state is supplied.
Counts are properties of this construction, not intrinsic costs of a unitary,
physical gate counts, or counts of bit-flip oracle calls.
-/

@[expose] public section

namespace QFixLean.PiOverThree

/-- The unoptimized expression from P05 v1, Section 4, equation (3).
Multiplication is operator order: the rightmost factor executes first. -/
def searchConstruction : ℕ → Construction
  | 0 => .base
  | k + 1 =>
      searchConstruction k * .source * (searchConstruction k).adjoint *
        .target * searchConstruction k

@[simp]
theorem searchConstruction_zero : searchConstruction 0 = .base := rfl

theorem searchConstruction_succ (k : ℕ) :
    searchConstruction (k + 1) =
      searchConstruction k * .source * (searchConstruction k).adjoint *
        .target * searchConstruction k := rfl

@[simp]
theorem searchConstruction_targetQueries_zero : (searchConstruction 0).targetQueries = 0 := rfl

@[simp]
theorem searchConstruction_baseCalls_zero : (searchConstruction 0).baseCalls = 1 := rfl

@[simp]
theorem searchConstruction_sourceCalls_zero : (searchConstruction 0).sourceCalls = 0 := rfl

/-- The inverse subconstruction has the same query cost as the forward one. -/
theorem searchConstruction_targetQueries_succ (k : ℕ) :
    (searchConstruction (k + 1)).targetQueries =
      3 * (searchConstruction k).targetQueries + 1 := by
  simp only [searchConstruction_succ, Construction.targetQueries,
    Construction.count_mul, Construction.count_adjoint]
  simp [Construction.source, Construction.target]
  omega

theorem searchConstruction_baseCalls_succ (k : ℕ) :
    (searchConstruction (k + 1)).baseCalls = 3 * (searchConstruction k).baseCalls := by
  simp only [searchConstruction_succ, Construction.baseCalls,
    Construction.count_mul, Construction.count_adjoint]
  simp [Construction.source, Construction.target]
  omega

theorem searchConstruction_sourceCalls_succ (k : ℕ) :
    (searchConstruction (k + 1)).sourceCalls =
      3 * (searchConstruction k).sourceCalls + 1 := by
  simp only [searchConstruction_succ, Construction.sourceCalls,
    Construction.count_mul, Construction.count_adjoint]
  simp [Construction.source, Construction.target]
  omega

/-- A subtraction-free identity, useful for both exact division and probabilities. -/
theorem searchConstruction_targetQueries_identity (k : ℕ) :
    2 * (searchConstruction k).targetQueries + 1 = (3 : ℕ) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [searchConstruction_targetQueries_succ, pow_succ]
    omega

/-- Natural subtraction and division are exact here by the preceding identity. -/
theorem searchConstruction_targetQueries (k : ℕ) :
    (searchConstruction k).targetQueries = ((3 : ℕ) ^ k - 1) / 2 := by
  rw [← searchConstruction_targetQueries_identity k]
  omega

/-- Count both base preparation calls and calls of its inverse. -/
theorem searchConstruction_baseCalls (k : ℕ) :
    (searchConstruction k).baseCalls = (3 : ℕ) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [searchConstruction_baseCalls_succ, ih, pow_succ, Nat.mul_comm]

/-- Source phases have a separate cost even though they are not target queries. -/
theorem searchConstruction_sourceCalls (k : ℕ) :
    (searchConstruction k).sourceCalls = (searchConstruction k).targetQueries := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [searchConstruction_sourceCalls_succ, searchConstruction_targetQueries_succ, ih]

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Exact native-unitary semantics, not just equality of measurement probabilities. -/
theorem interpret_searchConstruction (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    Construction.interpret U s hP (searchConstruction k) = searchRecursion U s hP k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [searchConstruction_succ, Construction.interpret_mul,
      Construction.interpret_source, Construction.interpret_target,
      Construction.interpret_adjoint, ih]
    rfl

/-- The construction and the existing algorithm act identically on every vector. -/
theorem searchConstruction_apply (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) (v : E) :
    (Construction.interpret U s hP (searchConstruction k) : E →L[ℂ] E) v =
      (searchRecursion U s hP k : E →L[ℂ] E) v := by
  rw [interpret_searchConstruction]

theorem searchConstruction_normalized (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    ‖(Construction.interpret U s hP (searchConstruction k) : E →L[ℂ] E) (s : E)‖ = 1 := by
  rw [interpret_searchConstruction]
  exact searchRecursion_normalized U s hP k

/-- P05 v1, following equation (4): failure in terms of this construction's queries. -/
theorem searchConstruction_failureWeight (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    failureWeight P
      ((Construction.interpret U s hP (searchConstruction k) : E →L[ℂ] E) (s : E)) =
      failureWeight P ((U : E →L[ℂ] E) (s : E)) ^
        (2 * (searchConstruction k).targetQueries + 1) := by
  rw [interpret_searchConstruction, searchRecursion_failureWeight,
    searchConstruction_targetQueries_identity]

theorem searchConstruction_successWeight (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    successWeight P
      ((Construction.interpret U s hP (searchConstruction k) : E →L[ℂ] E) (s : E)) =
      1 - failureWeight P ((U : E →L[ℂ] E) (s : E)) ^
        (2 * (searchConstruction k).targetQueries + 1) := by
  rw [interpret_searchConstruction, searchRecursion_successWeight,
    searchConstruction_targetQueries_identity]

/-- Semantics, normalization, costs and probabilities of one and the same construction.
There is no nondegeneracy assumption; convergence is a separate M09 result. -/
theorem searchConstruction_spec (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    let C := searchConstruction k
    let W := Construction.interpret U s hP C
    let ε := failureWeight P ((U : E →L[ℂ] E) (s : E))
    W = searchRecursion U s hP k ∧
      ‖(W : E →L[ℂ] E) (s : E)‖ = 1 ∧
      C.targetQueries = ((3 : ℕ) ^ k - 1) / 2 ∧
      C.baseCalls = (3 : ℕ) ^ k ∧
      C.sourceCalls = C.targetQueries ∧
      failureWeight P ((W : E →L[ℂ] E) (s : E)) = ε ^ (2 * C.targetQueries + 1) ∧
      successWeight P ((W : E →L[ℂ] E) (s : E)) = 1 - ε ^ (2 * C.targetQueries + 1) :=
  ⟨interpret_searchConstruction U s hP k, searchConstruction_normalized U s hP k,
    searchConstruction_targetQueries k, searchConstruction_baseCalls k,
    searchConstruction_sourceCalls k, searchConstruction_failureWeight U s hP k,
    searchConstruction_successWeight U s hP k⟩

end
end QFixLean.PiOverThree
