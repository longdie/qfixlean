module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# A division-free scaled Chebyshev recurrence

The recurrence is defined over complex polynomials. Its identification with
Mathlib's first-kind Chebyshev polynomials requires only a nonzero scale.
This supplies the constant-domino weights for the quasi-Chebyshev identity.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial

/-- The scaled recurrence has singleton weight `X` initially and `2*X`
thereafter, and a constant domino factor `-γ²`. -/
def scaledChebyshev (γ : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * scaledChebyshev γ (n + 1) - C (γ ^ 2) * scaledChebyshev γ n

@[simp] theorem scaledChebyshev_zero (γ : ℂ) : scaledChebyshev γ 0 = 1 := rfl

@[simp] theorem scaledChebyshev_one (γ : ℂ) : scaledChebyshev γ 1 = X := rfl

theorem scaledChebyshev_recurrence (γ : ℂ) (n : ℕ) :
    scaledChebyshev γ (n + 2) =
      2 * X * scaledChebyshev γ (n + 1) - C (γ ^ 2) * scaledChebyshev γ n := rfl

/-- Scaling the Mathlib recurrence gives the division-free recurrence above. -/
theorem scaledChebyshev_eq (γ : ℂ) (hγ : γ ≠ 0) (n : ℕ) :
    scaledChebyshev γ n =
      C (γ ^ n) * (Polynomial.Chebyshev.T ℂ (n : ℤ)).comp (C γ⁻¹ * X) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [scaledChebyshev_one, Nat.cast_one, Polynomial.Chebyshev.T_one,
      X_comp, pow_one]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hγ, C_1, one_mul]
  | more n ih₀ ih₁ =>
    rw [scaledChebyshev_recurrence, ih₀, ih₁]
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
      Polynomial.Chebyshev.T_add_two]
    simp only [sub_comp, mul_comp, X_comp, ofNat_comp]
    simp only [Nat.cast_add, Nat.cast_one]
    have hp : (C (γ ^ (n + 2)) : Polynomial ℂ) * C γ⁻¹ = C (γ ^ (n + 1)) := by
      rw [← C_mul, show γ ^ (n + 2) * γ⁻¹ = γ ^ (n + 1) by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, mul_assoc,
          mul_inv_cancel₀ hγ, mul_one]]
    have hq : (C (γ ^ 2) : Polynomial ℂ) * C (γ ^ n) = C (γ ^ (n + 2)) := by
      rw [← C_mul, mul_comm, ← pow_add]
    linear_combination -2 * X *
      (Polynomial.Chebyshev.T ℂ ((n : ℤ) + 1)).comp (C γ⁻¹ * X) * hp +
      -(Polynomial.Chebyshev.T ℂ (n : ℤ)).comp (C γ⁻¹ * X) * hq

end
end QFixLean.QuasiChebyshev
