module

public import QFixLean.Polynomial.QuasiChebyshevAlgebra
public import QFixLean.Polynomial.QuasiChebyshevPhases
import Mathlib.Tactic.Ring

/-!
# Algebraic preparation for the specified quasi-Chebyshev phases

Reference: P24, arXiv:2403.02057v3, Section 4.1, PDF equations (30)--(40)
(HTML (31)--(41)) and Remark 1. A complete schedule has `L = 2*ℓ+1` and
uses angles `φ₁,…,φ₂ℓ`. Its terminal amplitude is exactly `N_L(x)/D_L`.

The algebra below holds even for arbitrary real `γ`; the paper uses
`0 < γ ≤ 1`. Tangent pole avoidance is independently proved for odd `L`.
The terminal Chebyshev identification is proved in `QuasiChebyshevIdentity`.
No physical circuit phase convention is inferred by this algebra module.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial

/-- A prefix of the specified recurrence angles, with first index one. -/
def specifiedPrefix (L : ℕ) (γ : ℝ) (n : ℕ) : List ℝ :=
  phasePrefix (tangent L γ) n

@[simp] theorem specifiedPrefix_zero (L : ℕ) (γ : ℝ) : specifiedPrefix L γ 0 = [] := rfl

theorem specifiedPrefix_succ (L : ℕ) (γ : ℝ) (n : ℕ) :
    specifiedPrefix L γ (n + 1) = specifiedPrefix L γ n ++ [angle L γ (n + 1)] := rfl

@[simp] theorem specifiedPrefix_length (L : ℕ) (γ : ℝ) (n : ℕ) :
    (specifiedPrefix L γ n).length = n := phasePrefix_length _ _

/-- No phase at index zero is fed into the recurrence. -/
theorem specifiedPrefix_one (L : ℕ) (γ : ℝ) :
    specifiedPrefix L γ 1 = [angle L γ 1] := rfl

/-- The finite sequence used in the quasi-Chebyshev lemma. -/
def terminalPhases (ℓ : ℕ) (γ : ℝ) : List ℝ := specifiedPrefix (2 * ℓ + 1) γ (2 * ℓ)

@[simp] theorem terminalPhases_length (ℓ : ℕ) (γ : ℝ) :
    (terminalPhases ℓ γ).length = 2 * ℓ := specifiedPrefix_length _ _ _

/-- Every tangent used by the positive odd schedule avoids a pole. -/
theorem terminal_cos_ne_zero (ℓ n : ℕ) (hn : n < 2 * ℓ + 1) :
    Real.cos ((n : ℝ) * Real.pi / ((2 * ℓ + 1 : ℕ) : ℝ)) ≠ 0 := by
  apply cos_ne_zero_of_odd (by omega) _ hn
  exact ⟨ℓ, by omega⟩

theorem specified_denominator_ne_zero (L : ℕ) (γ : ℝ) (n : ℕ) :
    denominatorProduct (tangent L γ) n ≠ 0 := denominatorProduct_ne_zero _ _

@[simp] theorem specified_numerator_one (L : ℕ) (γ : ℝ) :
    numerator (tangent L γ) 1 = X := numerator_one _ (tangent_zero L γ)

/-- The cleared recurrence specialized to the paper's tangent sequence. -/
theorem specified_numerator_recurrence (L : ℕ) (γ : ℝ) (n : ℕ) :
    numerator (tangent L γ) (n + 2) =
      2 * X * numerator (tangent L γ) (n + 1) -
        C ((1 - Complex.I * (tangent L γ (n + 1) : ℂ)) *
          (1 + Complex.I * (tangent L γ n : ℂ))) * numerator (tangent L γ) n :=
  numerator_recurrence _ _

/-- Rational coefficients describe the original, uncleared amplitude. -/
theorem specified_amplitude_recurrence (L : ℕ) (γ : ℝ) (n : ℕ) (x : ℂ) :
    (amplitudePolynomial (tangent L γ) (n + 2)).eval x =
      (2 * x / (1 + Complex.I * (tangent L γ (n + 1) : ℂ))) *
        (amplitudePolynomial (tangent L γ) (n + 1)).eval x -
      ((1 - Complex.I * (tangent L γ (n + 1) : ℂ)) /
        (1 + Complex.I * (tangent L γ (n + 1) : ℂ))) *
          (amplitudePolynomial (tangent L γ) n).eval x := by
  rw [amplitudePolynomial_recurrence]
  simp only [eval_sub, eval_mul, eval_C, eval_X, PhaseRecurrence.coefficient]
  rw [one_add_phaseFactor_neg_two_arctan, phaseFactor_neg_two_arctan]
  ring

/-- A prefix of `n` specified angles returns the term with index `n+1`. -/
theorem specified_value (L : ℕ) (γ : ℝ) (n : ℕ) (x : ℂ) :
    PhaseRecurrence.value x (specifiedPrefix L γ n) =
      (numerator (tangent L γ) (n + 1)).eval x /
        denominatorProduct (tangent L γ) (n + 1) := value_phasePrefix _ _ _

/-- The same indexing in terms of an arbitrary positive length `L`. -/
theorem specified_value_length (L : ℕ) (hL : 0 < L) (γ : ℝ) (x : ℂ) :
    PhaseRecurrence.value x (specifiedPrefix L γ (L - 1)) =
      (numerator (tangent L γ) L).eval x / denominatorProduct (tangent L γ) L := by
  simpa only [Nat.sub_add_cancel hL] using specified_value L γ (L - 1) x

/-- The terminal identity is about the existing M13 recurrence for any complex x. -/
theorem terminal_value (ℓ : ℕ) (γ : ℝ) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases ℓ γ) =
      (numerator (tangent (2 * ℓ + 1) γ) (2 * ℓ + 1)).eval x /
        denominatorProduct (tangent (2 * ℓ + 1) γ) (2 * ℓ + 1) :=
  specified_value _ _ _ _

/-- Normalization follows from M13 at x=1, independently of any Chebyshev identity. -/
theorem specified_numerator_eval_one (L : ℕ) (γ : ℝ) (n : ℕ) :
    (numerator (tangent L γ) n).eval 1 = denominatorProduct (tangent L γ) n :=
  numerator_eval_one _ _

@[simp] theorem specifiedPrefix_gamma_one (L n : ℕ) :
    specifiedPrefix L 1 n = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [specifiedPrefix_succ, angle_gamma_one, ih, List.replicate_succ]
                 simpa only [List.replicate_succ, List.replicate_zero, List.singleton_append] using
                   (List.replicate_append_replicate (n := n) (m := 1) (a := (0 : ℝ)))

@[simp] theorem denominatorProduct_gamma_one (L n : ℕ) :
    denominatorProduct (tangent L 1) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [denominatorProduct_succ, ih]

/-- The parameter endpoint has the ordinary Chebyshev recurrence. The general
specified-phase identity is proved in `QuasiChebyshevIdentity`. -/
theorem numerator_recurrence_gamma_one (L n : ℕ) :
    numerator (tangent L 1) (n + 2) =
      2 * X * numerator (tangent L 1) (n + 1) - numerator (tangent L 1) n := by
  simp [numerator_recurrence]

end
end QFixLean.QuasiChebyshev
