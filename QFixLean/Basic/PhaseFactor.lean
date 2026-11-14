module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Scalar phase factors

Real angles use the positive convention `exp (I * φ)`. The exact values at π
and π/3 are consequences of the exponential definition and Mathlib's
trigonometric identities, not assumptions about an abstract root of unity.
-/

@[expose] public section

namespace QFixLean

noncomputable section

/-- The unit-modulus scalar for a real phase angle. -/
def phaseFactor (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))

@[simp]
theorem phaseFactor_zero : phaseFactor 0 = 1 := by
  simp [phaseFactor]

theorem phaseFactor_add (φ θ : ℝ) :
    phaseFactor (φ + θ) = phaseFactor φ * phaseFactor θ := by
  simp only [phaseFactor, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phaseFactor_neg (φ : ℝ) : phaseFactor (-φ) = star (phaseFactor φ) := by
  simp only [phaseFactor, Complex.ofReal_neg, mul_neg, Complex.star_def,
    ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

@[simp]
theorem phaseFactor_norm (φ : ℝ) : ‖phaseFactor φ‖ = 1 := by
  simpa only [phaseFactor, mul_comm] using Complex.norm_exp_ofReal_mul_I φ

theorem phaseFactor_star_mul_self (φ : ℝ) : star (phaseFactor φ) * phaseFactor φ = 1 := by
  rw [← phaseFactor_neg, ← phaseFactor_add, neg_add_cancel, phaseFactor_zero]

@[simp]
theorem phaseFactor_pi : phaseFactor Real.pi = -1 := by
  simpa only [phaseFactor, mul_comm] using Complex.exp_pi_mul_I

theorem phaseFactor_pi_div_three :
    phaseFactor (Real.pi / 3) =
      (1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  rw [phaseFactor, mul_comm Complex.I, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_comm]

/-- The scalar cancellation used later in the π/3 search proof. -/
theorem phaseFactor_pi_div_three_sub_one_sq :
    (phaseFactor (Real.pi / 3) - 1) ^ 2 = -phaseFactor (Real.pi / 3) := by
  rw [phaseFactor_pi_div_three]
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

end
end QFixLean
