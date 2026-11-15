module

public import QFixLean.Polynomial.PhaseRecurrence
public import QFixLean.Polynomial.PhaseRationalization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Clearing the denominators of the inverse-tangent phase recurrence

Reference: Li, Feng, Li, arXiv:2403.02057v3, Section 4.1, PDF equations
(38)--(40) and Remark 1. The real sequence `t` is arbitrary; only the
initial-term results need `t 0 = 0`.

The original polynomials are M13's `PhaseRecurrence.polynomial`, evaluated
on the first `n` angles. Thus an empty prefix ends at index one. No
Chebyshev identity or quantum output formula is assumed here.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial
open scoped BigOperators

/-- The first `n` recurrence angles, starting at index one. -/
def phasePrefix (t : ℕ → ℝ) : ℕ → List ℝ
  | 0 => []
  | n + 1 => phasePrefix t n ++ [2 * Real.arctan (t (n + 1))]

@[simp] theorem phasePrefix_zero (t : ℕ → ℝ) : phasePrefix t 0 = [] := rfl

theorem phasePrefix_succ (t : ℕ → ℝ) (n : ℕ) :
    phasePrefix t (n + 1) = phasePrefix t n ++ [2 * Real.arctan (t (n + 1))] := rfl

@[simp] theorem phasePrefix_length (t : ℕ → ℝ) (n : ℕ) : (phasePrefix t n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [phasePrefix_succ, ih]

/-- `A₀=1`, while `Aₙ₊₁` is M13's polynomial for the first `n` angles. -/
def amplitudePolynomial (t : ℕ → ℝ) : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => PhaseRecurrence.polynomial (phasePrefix t n)

@[simp] theorem amplitudePolynomial_zero (t : ℕ → ℝ) :
    amplitudePolynomial t 0 = 1 := rfl

@[simp] theorem amplitudePolynomial_one (t : ℕ → ℝ) :
    amplitudePolynomial t 1 = X := rfl

theorem amplitudePolynomial_succ (t : ℕ → ℝ) (n : ℕ) :
    amplitudePolynomial t (n + 1) = PhaseRecurrence.polynomial (phasePrefix t n) := rfl

/-- The same second-order recurrence, with successor indexing throughout. -/
theorem amplitudePolynomial_recurrence (t : ℕ → ℝ) (n : ℕ) :
    amplitudePolynomial t (n + 2) =
      C (1 + PhaseRecurrence.coefficient (2 * Real.arctan (t (n + 1)))) * X *
        amplitudePolynomial t (n + 1) -
      C (PhaseRecurrence.coefficient (2 * Real.arctan (t (n + 1)))) *
        amplitudePolynomial t n := by
  cases n with
  | zero =>
    simp [amplitudePolynomial, phasePrefix, PhaseRecurrence.polynomial,
      PhaseRecurrence.polynomialState, PhaseRecurrence.polynomialStep]
  | succ n =>
    exact PhaseRecurrence.polynomial_snoc_snoc (phasePrefix t n)
      (2 * Real.arctan (t (n + 1))) (2 * Real.arctan (t (n + 1 + 1)))

/-- `Dₙ` includes `t₀,…,tₙ₋₁` and is independent of the input variable. -/
def denominatorProduct (t : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 + Complex.I * (t k : ℂ))

@[simp] theorem denominatorProduct_zero (t : ℕ → ℝ) : denominatorProduct t 0 = 1 := by
  simp [denominatorProduct]

theorem denominatorProduct_succ (t : ℕ → ℝ) (n : ℕ) :
    denominatorProduct t (n + 1) =
      denominatorProduct t n * (1 + Complex.I * (t n : ℂ)) := by
  exact Finset.prod_range_succ _ _

@[simp] theorem denominatorProduct_one (t : ℕ → ℝ) (ht : t 0 = 0) :
    denominatorProduct t 1 = 1 := by
  simp [denominatorProduct_succ, ht]

theorem denominatorProduct_ne_zero (t : ℕ → ℝ) (n : ℕ) :
    denominatorProduct t n ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => one_add_I_mul_ne_zero (t k))

/-- The numerator is formed from the original recurrence, not a new algorithm. -/
def numerator (t : ℕ → ℝ) (n : ℕ) : Polynomial ℂ :=
  C (denominatorProduct t n) * amplitudePolynomial t n

theorem numerator_eq (t : ℕ → ℝ) (n : ℕ) :
    numerator t n = C (denominatorProduct t n) * amplitudePolynomial t n := rfl

@[simp] theorem numerator_zero (t : ℕ → ℝ) : numerator t 0 = 1 := by
  simp [numerator]

@[simp] theorem numerator_one (t : ℕ → ℝ) (ht : t 0 = 0) : numerator t 1 = X := by
  simp [numerator, ht]

private theorem factor_mul_coefficient (u : ℝ) :
    (1 + Complex.I * (u : ℂ)) * PhaseRecurrence.coefficient (2 * Real.arctan u) =
      1 - Complex.I * (u : ℂ) := by
  rw [PhaseRecurrence.coefficient, phaseFactor_neg_two_arctan]
  exact mul_div_cancel₀ _ (one_add_I_mul_ne_zero u)

private theorem factor_mul_one_add_coefficient (u : ℝ) :
    (1 + Complex.I * (u : ℂ)) * (1 + PhaseRecurrence.coefficient (2 * Real.arctan u)) =
      2 := by
  rw [mul_add, mul_one, factor_mul_coefficient]
  ring

/-- Exact denominator clearing. Both adjacent tangent indices are retained. -/
theorem numerator_recurrence (t : ℕ → ℝ) (n : ℕ) :
    numerator t (n + 2) = 2 * X * numerator t (n + 1) -
      C ((1 - Complex.I * (t (n + 1) : ℂ)) * (1 + Complex.I * (t n : ℂ))) *
        numerator t n := by
  have h₁ := congrArg (C : ℂ → Polynomial ℂ) (factor_mul_one_add_coefficient (t (n + 1)))
  have h₂ := congrArg (C : ℂ → Polynomial ℂ) (factor_mul_coefficient (t (n + 1)))
  rw [C_mul, map_ofNat] at h₁
  rw [C_mul] at h₂
  rw [numerator, amplitudePolynomial_recurrence, denominatorProduct_succ]
  simp only [C_mul, mul_sub]
  rw [show C (denominatorProduct t (n + 1)) * C (1 + Complex.I * (t (n + 1) : ℂ)) *
        (C (1 + PhaseRecurrence.coefficient (2 * Real.arctan (t (n + 1)))) * X *
          amplitudePolynomial t (n + 1)) =
      (C (1 + Complex.I * (t (n + 1) : ℂ)) *
        C (1 + PhaseRecurrence.coefficient (2 * Real.arctan (t (n + 1))))) * X *
          (C (denominatorProduct t (n + 1)) * amplitudePolynomial t (n + 1)) by ring,
    h₁]
  simp only [numerator, denominatorProduct_succ, C_mul]
  rw [show C (denominatorProduct t n) * C (1 + Complex.I * (t n : ℂ)) *
        C (1 + Complex.I * (t (n + 1) : ℂ)) *
        (C (PhaseRecurrence.coefficient (2 * Real.arctan (t (n + 1)))) *
          amplitudePolynomial t n) =
      (C (1 + Complex.I * (t (n + 1) : ℂ)) *
        C (PhaseRecurrence.coefficient (2 * Real.arctan (t (n + 1))))) *
          C (1 + Complex.I * (t n : ℂ)) *
          (C (denominatorProduct t n) * amplitudePolynomial t n) by ring, h₂]

/-- Polynomial recovery uses inverse scalar multiplication, not polynomial division. -/
theorem amplitudePolynomial_eq_inv_mul (t : ℕ → ℝ) (n : ℕ) :
    amplitudePolynomial t n = C ((denominatorProduct t n)⁻¹) * numerator t n := by
  rw [numerator, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (denominatorProduct_ne_zero t n)]
  simp

theorem amplitudePolynomial_eval (t : ℕ → ℝ) (n : ℕ) (x : ℂ) :
    (amplitudePolynomial t n).eval x = (numerator t n).eval x / denominatorProduct t n := by
  rw [numerator, eval_mul, eval_C, mul_div_cancel_left₀ _ (denominatorProduct_ne_zero t n)]

/-- A prefix of `n` angles ends at `aₙ₊₁`. -/
theorem value_phasePrefix (t : ℕ → ℝ) (n : ℕ) (x : ℂ) :
    PhaseRecurrence.value x (phasePrefix t n) =
      (numerator t (n + 1)).eval x / denominatorProduct t (n + 1) := by
  rw [← PhaseRecurrence.polynomial_eval]
  exact amplitudePolynomial_eval t (n + 1) x

@[simp] theorem amplitudePolynomial_eval_one (t : ℕ → ℝ) (n : ℕ) :
    (amplitudePolynomial t n).eval 1 = 1 := by
  cases n with
  | zero => simp
  | succ n => simp [amplitudePolynomial_succ]

/-- The normalization identity does not assume a Chebyshev formula. -/
theorem numerator_eval_one (t : ℕ → ℝ) (n : ℕ) :
    (numerator t n).eval 1 = denominatorProduct t n := by
  simp [numerator]

end
end QFixLean.QuasiChebyshev
