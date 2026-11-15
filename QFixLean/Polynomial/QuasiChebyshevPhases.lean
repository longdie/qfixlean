module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Tangents and angles for the quasi-Chebyshev recurrence

The schedule follows P24, arXiv:2403.02057v3, §4.1, PDF equation (32).
The tangent is a total Lean function, so avoidance of its poles is proved
separately for positive odd lengths. These definitions do not assume a
Chebyshev formula or identify the angles with a physical circuit schedule.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

def tangent (L : ℕ) (γ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (1 - γ ^ 2) * Real.tan ((n : ℝ) * Real.pi / (L : ℝ))

def angle (L : ℕ) (γ : ℝ) (n : ℕ) : ℝ :=
  2 * Real.arctan (tangent L γ n)

@[simp]
theorem tangent_zero (L : ℕ) (γ : ℝ) : tangent L γ 0 = 0 := by
  simp [tangent]

@[simp]
theorem tangent_gamma_one (L n : ℕ) : tangent L 1 n = 0 := by
  simp [tangent]

@[simp]
theorem angle_zero (L : ℕ) (γ : ℝ) : angle L γ 0 = 0 := by
  simp [angle]

@[simp]
theorem angle_gamma_one (L n : ℕ) : angle L 1 n = 0 := by
  simp [angle]

/-- Odd lengths avoid every tangent pole at the indices used by the recurrence. -/
theorem cos_ne_zero_of_odd {L n : ℕ} (hL : 0 < L) (hodd : Odd L) (hn : n < L) :
    Real.cos ((n : ℝ) * Real.pi / (L : ℝ)) ≠ 0 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hnr : (n : ℝ) < L := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ) * Real.pi / L := by positivity
  have hxπ : (n : ℝ) * Real.pi / L < Real.pi := by
    apply (div_lt_iff₀ hLr).2
    nlinarith [Real.pi_pos]
  intro hc
  have heq : (n : ℝ) * Real.pi / L = Real.pi / 2 := by
    apply Real.strictAntiOn_cos.injOn ⟨hx0, hxπ.le⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    simpa using hc
  have hmul := (div_eq_iff hLr.ne').mp heq
  have hcast : 2 * (n : ℝ) = (L : ℝ) := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    nlinarith
  have hnat : 2 * n = L := by exact_mod_cast hcast
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Reflection in a complete schedule reverses the tangent sign. -/
theorem tangent_reflection {L n : ℕ} (hL : 0 < L) (hn : n ≤ L) (γ : ℝ) :
    tangent L γ (L - n) = -tangent L γ n := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have harg : ((L - n : ℕ) : ℝ) * Real.pi / (L : ℝ) =
      Real.pi - (n : ℝ) * Real.pi / (L : ℝ) := by
    rw [Nat.cast_sub hn]
    field_simp
  simp only [tangent, harg, Real.tan_pi_sub, mul_neg]

end
end QFixLean.QuasiChebyshev
