module

public import QFixLean.PiOverThree.Step

/-!
# Recursive π/3 search

Reference: Grover, *A different kind of quantum search*, quant-ph/0503205v1,
Section 4, equation (3), and the probability formula following equation (4).

`searchRecursion U s hP k` is the actual unitary at level `k`. The source `s`
and target `P` remain fixed; each output is that level's operator applied to
the same `s`. The single-step theorem gives failure probability `ε₀^(3^k)`.
Endpoint behavior is developed in `Boundary.lean`, and monotonicity and
probability/complement-norm convergence in `Convergence.lean`.
Resource counts are separate later work.
-/

@[expose] public section

namespace QFixLean.PiOverThree

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- P05 v1, Section 4, equation (3): recursively replace the current unitary by
its π/3 search step, keeping the original source and target fixed. -/
def searchRecursion (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : ℕ → unitary (E →L[ℂ] E)
  | 0 => U
  | k + 1 => searchStep (searchRecursion U s hP k) s hP

@[simp]
theorem searchRecursion_zero (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : searchRecursion U s hP 0 = U := rfl

theorem searchRecursion_succ (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    searchRecursion U s hP (k + 1) = searchStep (searchRecursion U s hP k) s hP := rfl

/-- The bundled successor has exactly the five-factor operator semantics.
In particular, the adjoint applies to the whole current recursive unitary. -/
theorem coe_searchRecursion_succ (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    (searchRecursion U s hP (k + 1) : E →L[ℂ] E) =
      (searchRecursion U s hP k : E →L[ℂ] E) *
        phaseRotation s.projection (Real.pi / 3) *
        star (searchRecursion U s hP k : E →L[ℂ] E) *
        phaseRotation P (Real.pi / 3) * (searchRecursion U s hP k : E →L[ℂ] E) := rfl

/-- Every level's actual underlying operator is unitary. -/
theorem searchRecursion_mem_unitary (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    (searchRecursion U s hP k : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
  (searchRecursion U s hP k).property

/-- The actual level-k output, obtained from the original source, is normalized. -/
theorem searchRecursion_normalized (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    ‖(searchRecursion U s hP k : E →L[ℂ] E) (s : E)‖ = 1 :=
  (Unitary.norm_map (searchRecursion U s hP k) _).trans s.normalized

/-- Cubing is derived from the actual recursive operator and the single-step
theorem, rather than used as a definition of the output probability. -/
theorem searchRecursion_failureWeight_succ (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    failureWeight P ((searchRecursion U s hP (k + 1) : E →L[ℂ] E) (s : E)) =
      failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) ^ 3 :=
  searchStep_failureWeight (searchRecursion U s hP k) s hP

/-- P05 v1, Section 4, following equation (4): the actual level-k failure
probability is the initial failure probability raised to the natural power 3^k.
There is no nonzero-component, target-rank or strict probability assumption. -/
theorem searchRecursion_failureWeight (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    failureWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) =
      failureWeight P ((U : E →L[ℂ] E) (s : E)) ^ ((3 : ℕ) ^ k) := by
  induction k with
  | zero => rw [searchRecursion_zero, pow_zero, pow_one]
  | succ k ih => rw [searchRecursion_failureWeight_succ, ih, ← pow_mul, pow_succ]

/-- The success probability of that same normalized recursive output. -/
theorem searchRecursion_successWeight (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (k : ℕ) :
    successWeight P ((searchRecursion U s hP k : E →L[ℂ] E) (s : E)) =
      1 - failureWeight P ((U : E →L[ℂ] E) (s : E)) ^ ((3 : ℕ) ^ k) := by
  have h := successWeight_add_failureWeight_of_norm_eq_one hP
    (searchRecursion_normalized U s hP k)
  rw [searchRecursion_failureWeight] at h
  exact (eq_sub_iff_add_eq).2 h

end
end QFixLean.PiOverThree
