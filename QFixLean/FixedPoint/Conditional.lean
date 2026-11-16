module

public import QFixLean.Polynomial.ChebyshevParameters
public import QFixLean.Basic.Probability
import Mathlib.Tactic.Linarith

/-!
# Conditional measurement guarantee from a Chebyshev formula

Reference: Yoder, Low, Chuang, arXiv:1409.3305v2, equation (1) and the
following promise-interval argument. The scalar analysis is proved in
`Polynomial.ChebyshevParameters`. Here `hFormula` explicitly assumes that the
actual output's failure weight equals that scalar formula. Establishing this
equality for the explicit P14/P24 phase sequence is proved separately in
`FixedPoint.Correctness`.

The input's success probability lies in `[0,1]` by normalization and the
orthogonal target projection. The output guarantee uses the same output's
success/failure complementarity. Targets may have arbitrary rank. The
conditional implication holds for every positive degree; connecting it to
the P14 sequence in `Correctness` uses the algorithm's positive odd degree.
-/

@[expose] public section

namespace QFixLean.FixedPoint

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Given the explicit formula for an actual normalized output, its failure
probability is at most `δ²` and its success probability is at least `1 - δ²`.
The formula is a genuine equality premise, not a proved phase-sequence result. -/
theorem conditional_error_guarantee (L : ℕ) (hL : 0 < L) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (ψ₀ ψ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (hpromise : 1 - (Chebyshev.parameter L δ) ^ 2 ≤ successWeight P (ψ₀ : E))
    (hFormula : failureWeight P (ψ : E) =
      Chebyshev.failureModel L δ (successWeight P (ψ₀ : E))) :
    failureWeight P (ψ : E) ≤ δ ^ 2 ∧
      1 - δ ^ 2 ≤ successWeight P (ψ : E) := by
  have hInitial := ψ₀.successWeight_mem_Icc hP
  have hf := (Chebyshev.failureModel_mem_Icc hL hδ hδ1 hInitial hpromise).2
  rw [← hFormula] at hf
  have hc := ψ.successWeight_add_failureWeight hP
  exact ⟨hf, by linarith⟩

end
end QFixLean.FixedPoint
