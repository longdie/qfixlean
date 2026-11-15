module

public import QFixLean.FixedPoint.Conditional
public import QFixLean.Examples.Measurement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact checks of the Chebyshev scalar and conditional interfaces

The cubic example has a negative signed amplitude, while its square is
positive. The degree-one state example below supplies the formula premise
by proof on an existing normalized qubit state; it does not implement a
nontrivial P14 phase sequence.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

/-- Evaluate Mathlib's actual degree-three polynomial using its recurrence. -/
theorem chebyshev_evalT_three (x : ℝ) : Chebyshev.evalT 3 x = 4 * x ^ 3 - 3 * x := by
  have hp : Polynomial.Chebyshev.T ℝ (3 : ℤ) =
      4 * Polynomial.X ^ 3 - 3 * Polynomial.X := by
    rw [show (3 : ℤ) = 1 + 2 by rfl, Polynomial.Chebyshev.T_add_two,
      show (1 : ℤ) + 1 = 2 by rfl, Polynomial.Chebyshev.T_two,
      Polynomial.Chebyshev.T_one]
    ring
  change (Polynomial.Chebyshev.T ℝ (3 : ℤ)).eval x = _
  rw [hp]
  simp

theorem chebyshev_three_at_two : Chebyshev.evalT 3 2 = 26 := by
  rw [chebyshev_evalT_three]
  norm_num

theorem chebyshev_three_at_half : Chebyshev.evalT 3 (1 / 2) = -1 := by
  rw [chebyshev_evalT_three]
  norm_num

theorem chebyshev_three_half_denominator : Chebyshev.denominator 3 (1 / 2) = 26 := by
  norm_num [Chebyshev.denominator, chebyshev_evalT_three]

/-- The signed amplitude is negative; taking its square is essential. -/
theorem chebyshev_three_half_quarter_amplitude :
    Chebyshev.amplitude 3 (1 / 2) (1 / 4) = -(1 / 26 : ℝ) := by
  norm_num [Chebyshev.amplitude, Chebyshev.denominator, chebyshev_evalT_three]

theorem chebyshev_three_half_quarter_square :
    Chebyshev.amplitude 3 (1 / 2) (1 / 4) ^ 2 = (1 / 676 : ℝ) := by
  rw [chebyshev_three_half_quarter_amplitude]
  norm_num

/-- The general interval bound gives the same magnitude bound as the direct
polynomial calculation, without assuming the numerator bound. -/
theorem chebyshev_three_half_quarter_bound :
    |Chebyshev.amplitude 3 (1 / 2) (1 / 4)| ≤ (1 / 26 : ℝ) := by
  have h := Chebyshev.abs_amplitude_le 3 (γ := (1 / 2 : ℝ)) (x := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [chebyshev_three_half_denominator] using h

/-- At degree one the existing rational state satisfies the formula by direct
probability evaluation; no algorithm formula is postulated for this example. -/
theorem rationalState_chebyshev_formula :
    failureWeight firstBasisTarget (rationalState : QubitSpace) =
      Chebyshev.failureModel 1 (4 / 5)
        (successWeight firstBasisTarget (rationalState : QubitSpace)) := by
  rw [rationalState_failure, rationalState_success,
    Chebyshev.failureModel_one_degree (by norm_num : (0 : ℝ) < 4 / 5)
      (by norm_num : (4 / 5 : ℝ) < 1)
      (by norm_num : (9 / 25 : ℝ) ∈ Set.Icc (0 : ℝ) 1)]
  norm_num

/-- The rational input lies exactly at the standard promise boundary. -/
theorem rationalState_chebyshev_promise_boundary :
    1 - (Chebyshev.parameter 1 (4 / 5)) ^ 2 =
      successWeight firstBasisTarget (rationalState : QubitSpace) := by
  rw [Chebyshev.parameter_one (by norm_num : (0 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 1), rationalState_success]
  norm_num

/-- Apply the general conditional quantum interface with a proved premise,
using the same normalized state as input and output at degree one. -/
theorem rationalState_chebyshev_conditional_guarantee :
    failureWeight firstBasisTarget (rationalState : QubitSpace) ≤ (4 / 5 : ℝ) ^ 2 ∧
      1 - (4 / 5 : ℝ) ^ 2 ≤ successWeight firstBasisTarget (rationalState : QubitSpace) := by
  exact FixedPoint.conditional_error_guarantee 1 (by norm_num) (4 / 5)
    (by norm_num) (by norm_num) rationalState rationalState
    firstBasisTarget_isStarProjection rationalState_chebyshev_promise_boundary.le
    rationalState_chebyshev_formula

/-- The guarantee is saturated: there is no amplification at degree one. -/
theorem rationalState_chebyshev_exact_probabilities :
    failureWeight firstBasisTarget (rationalState : QubitSpace) = (4 / 5 : ℝ) ^ 2 ∧
      successWeight firstBasisTarget (rationalState : QubitSpace) = 1 - (4 / 5 : ℝ) ^ 2 := by
  rw [rationalState_failure, rationalState_success]
  norm_num

end
end QFixLean.Examples
