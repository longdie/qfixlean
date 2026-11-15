module

public import QFixLean.Basic.PhaseFactor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rational form of inverse-tangent phase factors

P24 v3 §4.1, PDF equations (33)–(38). These scalar identities hold for every
real tangent parameter; no interval restriction on an angle is assumed.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

theorem one_add_I_mul_ne_zero (t : ℝ) : (1 + Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_sub_I_mul_ne_zero (t : ℝ) : (1 - Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_sub_I_mul_mul_one_add_I_mul (t : ℝ) :
    (1 - Complex.I * (t : ℂ)) * (1 + Complex.I * (t : ℂ)) = 1 + (t : ℂ)^2 := by
  calc
    _ = 1 - Complex.I ^ 2 * (t : ℂ)^2 := by ring
    _ = _ := by simp

/-- The negative exponential sign is the one used by the amplitude recurrence. -/
theorem phaseFactor_neg_two_arctan (t : ℝ) :
    phaseFactor (-(2 * Real.arctan t)) =
      (1 - Complex.I * (t : ℂ)) / (1 + Complex.I * (t : ℂ)) := by
  apply (eq_div_iff (one_add_I_mul_ne_zero t)).2
  have hc : Real.cos (Real.arctan t) ≠ 0 := (Real.cos_arctan_pos t).ne'
  have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
    have ht := Real.tan_arctan t
    rw [Real.tan_eq_sin_div_cos] at ht
    exact (div_eq_iff hc).1 ht
  have hcircle := Real.sin_sq_add_cos_sq (Real.arctan t)
  rw [hs] at hcircle
  rw [phaseFactor, mul_comm Complex.I, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.sub_re, Complex.sub_im, Real.cos_neg, Real.sin_neg,
      Real.cos_two_mul, Real.sin_two_mul, hs] <;>
    nlinarith [hcircle, congrArg (fun u : ℝ => t * u) hcircle]

theorem one_add_phaseFactor_neg_two_arctan (t : ℝ) :
    1 + phaseFactor (-(2 * Real.arctan t)) = 2 / (1 + Complex.I * (t : ℂ)) := by
  rw [phaseFactor_neg_two_arctan]
  field_simp [one_add_I_mul_ne_zero t]
  ring

theorem one_add_I_mul_mul_phaseFactor_neg_two_arctan (t : ℝ) :
    (1 + Complex.I * (t : ℂ)) * phaseFactor (-(2 * Real.arctan t)) =
      1 - Complex.I * (t : ℂ) := by
  rw [phaseFactor_neg_two_arctan, mul_div_cancel₀ _ (one_add_I_mul_ne_zero t)]

theorem one_add_I_mul_mul_one_add_phaseFactor_neg_two_arctan (t : ℝ) :
    (1 + Complex.I * (t : ℂ)) * (1 + phaseFactor (-(2 * Real.arctan t))) = 2 := by
  rw [mul_add, mul_one, one_add_I_mul_mul_phaseFactor_neg_two_arctan]
  ring

@[simp]
theorem phaseFactor_neg_two_arctan_zero : phaseFactor (-(2 * Real.arctan 0)) = 1 := by
  simp

@[simp]
theorem phaseFactor_neg_two_arctan_one :
    phaseFactor (-(2 * Real.arctan 1)) = -Complex.I := by
  rw [phaseFactor_neg_two_arctan]
  apply (div_eq_iff (one_add_I_mul_ne_zero 1)).2
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im]

@[simp]
theorem phaseFactor_neg_two_arctan_neg_one :
    phaseFactor (-(2 * Real.arctan (-1))) = Complex.I := by
  rw [phaseFactor_neg_two_arctan]
  apply (div_eq_iff (one_add_I_mul_ne_zero (-1))).2
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im]

end
end QFixLean.QuasiChebyshev
