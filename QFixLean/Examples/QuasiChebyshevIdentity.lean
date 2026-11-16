module

public import QFixLean.Examples.QuasiChebyshev
public import QFixLean.Examples.Chebyshev
public import QFixLean.Polynomial.QuasiChebyshevIdentity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Independent exact checks of the quasi-Chebyshev identity

The first path computes the length-three schedule from the M13 recurrence
and the exact value of `tan (π/3)`, independently of the general M16 proof.
The signed amplitude remains negative in the rational example.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

open Polynomial QFixLean.QuasiChebyshev

/-- Exact tangent square on the complete real-square-root domain. -/
theorem cubicTangent_sq (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    cubicTangent γ ^ 2 = 3 * (1 - γ ^ 2) := by
  have hw : 0 ≤ 1 - γ ^ 2 := by nlinarith
  rw [cubicTangent, mul_pow, Real.tan_pi_div_three,
    Real.sq_sqrt hw, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem cubicTangent_complex_sq (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (cubicTangent γ : ℂ) ^ 2 = 3 * (1 - (γ : ℂ) ^ 2) := by
  exact_mod_cast cubicTangent_sq γ hγ hγ1

/-- Numerator obtained by the existing direct recurrence calculation. -/
theorem quasi_cubic_numerator_direct (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    numerator (tangent 3 γ) 3 =
      4 * X ^ 3 - 3 * C ((γ : ℂ) ^ 2) * X := by
  rw [cubic_numerator_three, cubicTangent_complex_sq γ hγ hγ1]
  simp only [map_sub, map_mul, map_ofNat, map_one]
  ring

/-- Denominator obtained from the same exact tangent square. -/
theorem quasi_cubic_denominator_direct (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    denominatorProduct (tangent 3 γ) 3 = 4 - 3 * (γ : ℂ) ^ 2 := by
  rw [cubic_denominator, cubicTangent_complex_sq γ hγ hγ1]
  ring

/-- Terminal value from the independent M13 expansion, without M16. -/
theorem quasi_cubic_value_direct (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases 1 γ) =
      (4 * x ^ 3 - 3 * (γ : ℂ) ^ 2 * x) / (4 - 3 * (γ : ℂ) ^ 2) := by
  rw [cubic_terminal_value, cubicTangent_complex_sq γ hγ hγ1]
  congr 1 <;> ring

/-- The actual two-angle recurrence has signed value `-1/26`. -/
theorem quasi_cubic_half_quarter_direct :
    PhaseRecurrence.value (1 / 4 : ℂ) (terminalPhases 1 (1 / 2)) = -(1 / 26 : ℂ) := by
  rw [quasi_cubic_value_direct (1 / 2) (by norm_num) (by norm_num)]
  norm_num

theorem quasi_cubic_half_quarter_norm_sq_direct :
    ‖PhaseRecurrence.value (1 / 4 : ℂ) (terminalPhases 1 (1 / 2))‖ ^ 2 = (1 / 676 : ℝ) := by
  rw [quasi_cubic_half_quarter_direct]
  norm_num

/-- Direct recurrence and the existing M11 scalar interface agree exactly. -/
theorem quasi_cubic_half_quarter_agrees_M11 :
    PhaseRecurrence.value (1 / 4 : ℂ) (terminalPhases 1 (1 / 2)) =
      (Chebyshev.amplitude 3 (1 / 2) (1 / 4) : ℂ) := by
  rw [quasi_cubic_half_quarter_direct, chebyshev_three_half_quarter_amplitude]
  norm_num

/-- A second path: specialize the proved general M16 Chebyshev identity,
then evaluate its scaled Mathlib recurrence. -/
theorem quasi_cubic_numerator_general (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    numerator (tangent 3 γ) 3 =
      4 * X ^ 3 - 3 * C ((γ : ℂ) ^ 2) * X := by
  rw [numerator_eq_scaledChebyshev (by decide : Odd 3) hγ hγ1,
    scaledChebyshev_recurrence _ 1, scaledChebyshev_recurrence _ 0]
  norm_num only [Nat.reduceAdd, scaledChebyshev_one, scaledChebyshev_zero]
  ring

/-- The general M16 numerator gives the denominator by evaluation at one. -/
theorem quasi_cubic_denominator_general (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    denominatorProduct (tangent 3 γ) 3 = 4 - 3 * (γ : ℂ) ^ 2 := by
  rw [← specified_numerator_eval_one 3 γ 3,
    quasi_cubic_numerator_general γ hγ hγ1]
  simp

/-- Recover the same terminal formula through the general M16 result. -/
theorem quasi_cubic_value_general (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases 1 γ) =
      (4 * x ^ 3 - 3 * (γ : ℂ) ^ 2 * x) / (4 - 3 * (γ : ℂ) ^ 2) := by
  rw [terminal_value]
  change (numerator (tangent 3 γ) 3).eval x /
    denominatorProduct (tangent 3 γ) 3 = _
  rw [quasi_cubic_numerator_general γ hγ hγ1,
    quasi_cubic_denominator_general γ hγ hγ1]
  simp

/-- The general real-amplitude bridge gives the signed rational value again. -/
theorem quasi_cubic_half_quarter_general :
    PhaseRecurrence.value (1 / 4 : ℂ) (terminalPhases 1 (1 / 2)) = -(1 / 26 : ℂ) := by
  have h := terminal_value_eq_amplitude 1 (γ := 1 / 2)
    (by norm_num) (by norm_num) (1 / 4)
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_one,
    chebyshev_three_half_quarter_amplitude, Complex.ofReal_neg,
    Complex.ofReal_ofNat] using h

/-- Both exact proofs compute the same recurrence; no formula is assumed. -/
theorem quasi_cubic_half_quarter_norm_sq_general :
    ‖PhaseRecurrence.value (1 / 4 : ℂ) (terminalPhases 1 (1 / 2))‖ ^ 2 = (1 / 676 : ℝ) := by
  have h := terminal_value_norm_sq 1 (γ := 1 / 2)
    (by norm_num) (by norm_num) (1 / 4)
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_one,
    chebyshev_three_half_quarter_square, Complex.ofReal_ofNat] using h

/-- Length one is included in the general theorem, not excluded as degenerate. -/
theorem quasi_length_one_general (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases 0 γ) =
      (Polynomial.Chebyshev.T ℂ 1).eval (x / (γ : ℂ)) /
        (Polynomial.Chebyshev.T ℂ 1).eval (1 / (γ : ℂ)) := by
  exact terminal_value_chebyshev 0 hγ hγ1 x

/-- The degree-one Chebyshev ratio itself reduces to `x`, in agreement with
the independently computed empty phase list. -/
theorem quasi_length_one_chebyshev_ratio (γ : ℝ) (hγ : 0 < γ) (x : ℂ) :
    (Polynomial.Chebyshev.T ℂ 1).eval (x / (γ : ℂ)) /
      (Polynomial.Chebyshev.T ℂ 1).eval (1 / (γ : ℂ)) = x := by
  have hc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  simp only [Polynomial.Chebyshev.T_one, eval_X]
  field_simp

/-- At gamma one the original zero-phase schedule has Chebyshev terminal value. -/
theorem quasi_gamma_one_terminal_chebyshev (ℓ : ℕ) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases ℓ 1) =
      (Polynomial.Chebyshev.T ℂ ((2 * ℓ + 1 : ℕ) : ℤ)).eval x := by
  rw [terminal_value_chebyshev ℓ (γ := 1) (by norm_num) (by norm_num)]
  simp

/-- Composite length nine is included without a prime-length or orbit premise. -/
theorem quasi_length_nine_numerator (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    numerator (tangent 9 γ) 9 = C ((γ : ℂ) ^ 9) *
      (Polynomial.Chebyshev.T ℂ 9).comp (C ((γ : ℂ)⁻¹) * X) :=
  numerator_chebyshev (by decide : Odd 9) hγ hγ1

/-- The complete length-nine schedule contains eight angles. -/
theorem quasi_length_nine_terminal (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases 4 γ) =
      (Polynomial.Chebyshev.T ℂ 9).eval (x / (γ : ℂ)) /
        (Polynomial.Chebyshev.T ℂ 9).eval (1 / (γ : ℂ)) :=
  terminal_value_chebyshev 4 hγ hγ1 x

end
end QFixLean.Examples
