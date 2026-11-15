module

public import QFixLean.Polynomial.QuasiChebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact checks for denominator clearing

These checks compare a direct M13 two-angle expansion with the new
numerator recurrence. The cubic example uses the actual P24 tangent
schedule. No complete Chebyshev identity is assumed.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

open Polynomial QFixLean.QuasiChebyshev

/-- Direct expansion of M13, independent of denominator clearing. -/
theorem arctan_pair_value_direct (r : ℝ) (x : ℂ) :
    PhaseRecurrence.value x [2 * Real.arctan r, 2 * Real.arctan (-r)] =
      (4 * x^3 + ((r : ℂ)^2 - 3) * x) / (1 + (r : ℂ)^2) := by
  have hp := one_add_I_mul_ne_zero r
  have hm := one_sub_I_mul_ne_zero r
  have hden : (1 + (r : ℂ)^2) ≠ 0 := by
    rw [← one_sub_I_mul_mul_one_add_I_mul]
    exact mul_ne_zero hm hp
  simp only [PhaseRecurrence.value, PhaseRecurrence.state, List.foldl_cons,
    List.foldl_nil, PhaseRecurrence.step, PhaseRecurrence.coefficient,
    phaseFactor_neg_two_arctan, Complex.ofReal_neg]
  simp only [mul_neg, ← sub_eq_add_neg]
  field_simp [hp, hm, hden]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem quasi_initial_terms (L : ℕ) (γ : ℝ) :
    amplitudePolynomial (tangent L γ) 0 = 1 ∧
    amplitudePolynomial (tangent L γ) 1 = X ∧
    denominatorProduct (tangent L γ) 0 = 1 ∧
    denominatorProduct (tangent L γ) 1 = 1 ∧
    numerator (tangent L γ) 0 = 1 ∧ numerator (tangent L γ) 1 = X := by
  simp [denominatorProduct_one _ (tangent_zero L γ),
    numerator_one _ (tangent_zero L γ)]

theorem quasi_one_two_angle_indices (t : ℕ → ℝ) :
    amplitudePolynomial t 2 = PhaseRecurrence.polynomial [2 * Real.arctan (t 1)] ∧
    amplitudePolynomial t 3 =
      PhaseRecurrence.polynomial [2 * Real.arctan (t 1), 2 * Real.arctan (t 2)] := by
  constructor <;> rfl

theorem quasi_short_denominators (t : ℕ → ℝ) (ht : t 0 = 0) :
    denominatorProduct t 2 = 1 + Complex.I * (t 1 : ℂ) ∧
    denominatorProduct t 3 =
      (1 + Complex.I * (t 1 : ℂ)) * (1 + Complex.I * (t 2 : ℂ)) := by
  rw [denominatorProduct_succ _ 2, denominatorProduct_succ _ 1,
    denominatorProduct_one _ ht]
  simp

theorem quasi_phase_signs :
    phaseFactor (-(2 * Real.arctan 0)) = 1 ∧
    phaseFactor (-(2 * Real.arctan 1)) = -Complex.I ∧
    phaseFactor (-(2 * Real.arctan (-1))) = Complex.I := by
  exact ⟨phaseFactor_neg_two_arctan_zero, phaseFactor_neg_two_arctan_one,
    phaseFactor_neg_two_arctan_neg_one⟩

/-- No iteration angle is used when the odd length is one. -/
theorem quasi_length_one (γ : ℝ) (x : ℂ) :
    phasePrefix (tangent 1 γ) 0 = [] ∧
    amplitudePolynomial (tangent 1 γ) 1 = X ∧
    numerator (tangent 1 γ) 1 = X ∧
    denominatorProduct (tangent 1 γ) 1 = 1 ∧
    PhaseRecurrence.value x (phasePrefix (tangent 1 γ) 0) = x := by
  simp [numerator_one _ (tangent_zero 1 γ),
    denominatorProduct_one _ (tangent_zero 1 γ)]

theorem quasi_terminal_length_one (γ : ℝ) (x : ℂ) :
    terminalPhases 0 γ = [] ∧ PhaseRecurrence.value x (terminalPhases 0 γ) = x := by
  simp [terminalPhases]

theorem quasi_gamma_one_phases (ℓ : ℕ) :
    terminalPhases ℓ 1 = List.replicate (2 * ℓ) 0 := by
  simp [terminalPhases]

theorem quasi_gamma_one_denominator (L n : ℕ) :
    denominatorProduct (tangent L 1) n = 1 := denominatorProduct_gamma_one _ _

theorem quasi_gamma_one_recurrence (L n : ℕ) :
    numerator (tangent L 1) (n + 2) =
      2 * X * numerator (tangent L 1) (n + 1) - numerator (tangent L 1) n :=
  numerator_recurrence_gamma_one _ _

/-- The first nonzero tangent of the length-three paper schedule. -/
def cubicTangent (γ : ℝ) : ℝ := Real.sqrt (1 - γ^2) * Real.tan (Real.pi / 3)

@[simp]
theorem cubic_tangent_one (γ : ℝ) : tangent 3 γ 1 = cubicTangent γ := by
  simp [tangent, cubicTangent]

@[simp]
theorem cubic_tangent_two (γ : ℝ) : tangent 3 γ 2 = -cubicTangent γ := by
  simpa using tangent_reflection (L := 3) (n := 1) (by norm_num) (by norm_num) γ

theorem cubic_prefix (γ : ℝ) :
    phasePrefix (tangent 3 γ) 2 =
      [2 * Real.arctan (cubicTangent γ), 2 * Real.arctan (-cubicTangent γ)] := by
  simp [phasePrefix]

theorem cubic_denominator (γ : ℝ) :
    denominatorProduct (tangent 3 γ) 3 = 1 + (cubicTangent γ : ℂ)^2 := by
  rw [denominatorProduct_succ _ 2, denominatorProduct_succ _ 1,
    denominatorProduct_one _ (tangent_zero 3 γ)]
  simp only [cubic_tangent_one, cubic_tangent_two, Complex.ofReal_neg, mul_neg,
    ← sub_eq_add_neg, one_mul]
  rw [mul_comm, one_sub_I_mul_mul_one_add_I_mul]

theorem cubic_numerator_two (γ : ℝ) :
    numerator (tangent 3 γ) 2 =
      2 * X^2 - C (1 - Complex.I * (cubicTangent γ : ℂ)) := by
  rw [numerator_recurrence _ 0]
  simp only [Nat.zero_add]
  simp only [numerator_one _ (tangent_zero 3 γ), numerator_zero, tangent_zero,
    cubic_tangent_one, Complex.ofReal_zero, mul_zero, add_zero, mul_one]
  ring

theorem cubic_numerator_three (γ : ℝ) :
    numerator (tangent 3 γ) 3 =
      4 * X^3 + C ((cubicTangent γ : ℂ)^2 - 3) * X := by
  rw [numerator_recurrence _ 1]
  change 2 * X * numerator (tangent 3 γ) 2 -
    C ((1 - Complex.I * (tangent 3 γ 2 : ℂ)) *
      (1 + Complex.I * (tangent 3 γ 1 : ℂ))) * numerator (tangent 3 γ) 1 = _
  rw [cubic_numerator_two, numerator_one _ (tangent_zero 3 γ)]
  simp only [cubic_tangent_one, cubic_tangent_two, Complex.ofReal_neg,
    mul_neg, sub_neg_eq_add, C_mul, map_add, map_one, map_sub, map_pow, map_ofNat]
  have hI : (C Complex.I : Polynomial ℂ)^2 = -1 := by
    rw [← C_pow]
    simp
  ring_nf
  simp only [hI]
  ring

/-- The paper's two-angle terminal value, computed from M13 alone. -/
theorem cubic_value_direct (γ : ℝ) (x : ℂ) :
    PhaseRecurrence.value x (phasePrefix (tangent 3 γ) 2) =
      (4 * x^3 + ((cubicTangent γ : ℂ)^2 - 3) * x) /
        (1 + (cubicTangent γ : ℂ)^2) := by
  rw [cubic_prefix]
  exact arctan_pair_value_direct _ _

/-- The same terminal value, computed by the numerator recurrence and recovery. -/
theorem cubic_value_cleared (γ : ℝ) (x : ℂ) :
    PhaseRecurrence.value x (phasePrefix (tangent 3 γ) 2) =
      (4 * x^3 + ((cubicTangent γ : ℂ)^2 - 3) * x) /
        (1 + (cubicTangent γ : ℂ)^2) := by
  rw [value_phasePrefix, cubic_numerator_three, cubic_denominator]
  simp

/-- The complete L=3 list has two angles and ends at amplitude index three. -/
theorem cubic_terminal_value (γ : ℝ) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases 1 γ) =
      (4 * x^3 + ((cubicTangent γ : ℂ)^2 - 3) * x) /
        (1 + (cubicTangent γ : ℂ)^2) := cubic_value_direct γ x

end
end QFixLean.Examples
