module

public import QFixLean.Polynomial.LineTilings
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact short-line checks

The empty line, one site, two sites and three sites have respectively one,
one, two and three actual layouts. Their finite weight sums agree with the
original M14 numerators. In particular the intermediate quadratic can have
a genuinely nonreal constant coefficient; no real-part projection is used.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

open Polynomial QFixLean.QuasiChebyshev

/-- Exact counts of the four initial physical layout types. -/
theorem line_initial_layout_counts :
    Fintype.card (LineTiling.Layout 0) = 1 ∧
    Fintype.card (LineTiling.Layout 1) = 1 ∧
    Fintype.card (LineTiling.Layout 2) = 2 ∧
    Fintype.card (LineTiling.Layout 3) = 3 := by
  decide

/-- Direct enumeration of the initial actual line sums. Both neighboring
complex factors are retained in the three-site domino coefficient. -/
theorem line_initial_weight_sums (t : ℕ → ℝ) (ht : t 0 = 0) :
    LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 0 = 1 ∧
    LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 1 = X ∧
    LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 2 =
      2 * X ^ 2 - C (1 - Complex.I * (t 1 : ℂ)) ∧
    LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 3 =
      4 * X ^ 3 - 2 * X * C (1 - Complex.I * (t 1 : ℂ)) -
        X * C ((1 - Complex.I * (t 2 : ℂ)) * (1 + Complex.I * (t 1 : ℂ))) := by
  constructor
  · exact LineTiling.total_zero _ _
  constructor
  · simp [LineTiling.modifiedSingleton]
  constructor
  · rw [LineTiling.total_two]
    simp only [LineTiling.modifiedSingleton, LineTiling.phaseDomino,
      Nat.sub_self, ht, Complex.ofReal_zero, mul_zero, add_zero,
      mul_one, ↓reduceIte, one_ne_zero]
    ring
  · rw [LineTiling.total_three]
    norm_num only [LineTiling.modifiedSingleton, LineTiling.phaseDomino,
      ht, Complex.ofReal_zero, mul_zero, add_zero, mul_one,
      Nat.reduceSub, ↓reduceIte]
    ring

/-- The four finite layout sums refer to the existing numerators, including
`N₀` rather than confusing the empty phase prefix with index zero. -/
theorem line_initial_numerator_correspondence (t : ℕ → ℝ) (ht : t 0 = 0) :
    (LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 0,
      LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 1,
      LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 2,
      LineTiling.total (LineTiling.modifiedSingleton X) (LineTiling.phaseDomino t) 3) =
    (numerator t 0, numerator t 1, numerator t 2, numerator t 3) := by
  simp only [LineTiling.total_eq_numerator t ht]

/-- A real tangent sequence whose intermediate numerator has a nonreal
constant coefficient. This is a short-line algebra check, not a terminal
Chebyshev claim. -/
def nonrealLineSequence (n : ℕ) : ℝ := if n = 1 then 1 else 0

/-- The imaginary coefficient of the actual two-site sum is exactly one. -/
theorem line_two_nonreal_constant :
    ((LineTiling.total (LineTiling.modifiedSingleton X)
      (LineTiling.phaseDomino nonrealLineSequence) 2).coeff 0).im = 1 := by
  have h := (line_initial_weight_sums nonrealLineSequence (by
    norm_num [nonrealLineSequence])).2.2.1
  rw [h]
  norm_num [nonrealLineSequence, coeff_mul_X_pow']

/-- The same nonreal coefficient belongs to M14's actual numerator. -/
theorem numerator_two_nonreal_constant :
    ((numerator nonrealLineSequence 2).coeff 0).im = 1 := by
  rw [← LineTiling.total_eq_numerator nonrealLineSequence (by
    norm_num [nonrealLineSequence])]
  exact line_two_nonreal_constant

end
end QFixLean.Examples
