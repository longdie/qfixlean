module

public import QFixLean.Polynomial.PhaseTilingWeights
public import QFixLean.Polynomial.LineCycleBridge
public import QFixLean.Polynomial.TilingWeights
public import QFixLean.Polynomial.QuasiChebyshev
public import QFixLean.Polynomial.ChebyshevBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The quasi-Chebyshev identity for the existing phase recurrence

Reference: Li, Feng, Li, arXiv:2403.02057v3, Section 4: PDF (41)--(42),
Lemmas 3 and 5--9 (HTML (42)--(43), Lemmas 4.1 and 4.5--4.13).

Actual finite line layouts give M14's numerator. Reflection doubles its
modified cut to the full circle. M15 and a permutation double sum compare
the circle weights to constant-domino weights, whose recurrence is the
scaled Mathlib Chebyshev recurrence. All rotations are counted, even when
the action has a nontrivial stabilizer. The denominator follows by evaluating
the numerator at one; no out-of-domain square-root substitution is used.

These are scalar identities. `FixedPoint.Correctness` connects them to the
explicit quantum phase schedule; oracle resources remain a separate task.
The general conditional quantum theorem is retained.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial
open scoped BigOperators

/-- The paper's cyclic domino coefficients reproduce the actual line sum. -/
theorem line_total_phase {L : ℕ} [NeZero L] (γ : ℝ) :
    LineTiling.total (LineTiling.modifiedSingleton X)
      (fun n => cyclicPhaseDomino γ (n : ZMod L)) L = numerator (tangent L γ) L := by
  rw [← LineTiling.total_eq_numerator _ (tangent_zero L γ)]
  exact LineTiling.total_congr (fun _ _ => rfl)
    (fun n hn _ => cyclicPhaseDomino_natCast γ n hn)

/-- The complete phase numerator is the scaled Chebyshev recurrence.
Only the terminal index `L` is asserted; intermediate numerators can be complex. -/
theorem numerator_eq_scaledChebyshev {L : ℕ} [NeZero L] (hodd : Odd L)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    numerator (tangent L γ) L = scaledChebyshev (γ : ℂ) L := by
  by_cases hL1 : L = 1
  · subst L
    simp
  have hL : 1 < L := by have := NeZero.ne L; omega
  have hphase : (∑ D : CyclicTiling L, cyclicWeight X (cyclicPhaseDomino γ) D.val) =
      2 * numerator (tangent L γ) L := by
    rw [← line_total_phase γ, total_eq_sum_cutWeight hL]
    exact sum_cyclicWeight_eq_twice_cut _
      (fun D => cyclicWeight_reflect X _ (cyclicPhaseDomino_reflect γ) D.val)
  have hconstant : (∑ D : CyclicTiling L,
      cyclicWeight X (fun _ => -C ((γ : ℂ) ^ 2)) D.val) =
      2 * scaledChebyshev (γ : ℂ) L := by
    calc
      _ = 2 * LineTiling.total (LineTiling.modifiedSingleton X)
          (fun _ => -C ((γ : ℂ) ^ 2)) L :=
        sum_cyclic_eq_twice_line hL X (fun _ => -C ((γ : ℂ) ^ 2)) (fun _ => rfl)
      _ = _ := by rw [line_total_constant]
  have hcompare := cyclic_tiling_weight_comparison hodd (Real.sqrt (1 - γ ^ 2) : ℂ)
  change (∑ D : CyclicTiling L, cyclicWeight X (cyclicPhaseDomino γ) D.val) = _ at hcompare
  simp only [one_sub_complex_tangentScale_sq hγ hγ1] at hcompare
  change _ = ∑ D : CyclicTiling L,
    cyclicWeight X (fun _ => -C ((γ : ℂ) ^ 2)) D.val at hcompare
  rw [hphase, hconstant] at hcompare
  have h2 : (2 : Polynomial ℂ) ≠ 0 := by
    intro hz
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hz
    norm_num at this
  exact mul_left_cancel₀ h2 hcompare

/-- The actual M14 numerator, for every positive odd length and `0 < γ ≤ 1`. -/
theorem numerator_chebyshev {L : ℕ} [NeZero L] (hodd : Odd L)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    numerator (tangent L γ) L = C ((γ : ℂ) ^ L) *
      (Polynomial.Chebyshev.T ℂ (L : ℤ)).comp (C ((γ : ℂ)⁻¹) * X) := by
  rw [numerator_eq_scaledChebyshev hodd hγ hγ1]
  exact scaledChebyshev_eq _ (by exact_mod_cast hγ.ne') L

/-- Normalization follows from the same numerator at input one. -/
theorem denominatorProduct_chebyshev {L : ℕ} [NeZero L] (hodd : Odd L)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    denominatorProduct (tangent L γ) L = (γ : ℂ) ^ L *
      (Polynomial.Chebyshev.T ℂ (L : ℤ)).eval (1 / (γ : ℂ)) := by
  rw [← specified_numerator_eval_one L γ L, numerator_chebyshev hodd hγ hγ1]
  simp

/-- The normalizing complex Chebyshev value is nonzero by the actual product. -/
theorem complex_chebyshev_denominator_ne_zero {L : ℕ} [NeZero L] (hodd : Odd L)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Polynomial.Chebyshev.T ℂ (L : ℤ)).eval (1 / (γ : ℂ)) ≠ 0 := by
  have h := specified_denominator_ne_zero L γ L
  rw [denominatorProduct_chebyshev hodd hγ hγ1] at h
  exact (mul_ne_zero_iff.mp h).2

/-- The existing prefix value, with its original `L-1` angle indexing. -/
theorem specified_value_chebyshev {L : ℕ} [NeZero L] (hodd : Odd L)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℂ) :
    PhaseRecurrence.value x (specifiedPrefix L γ (L - 1)) =
      (Polynomial.Chebyshev.T ℂ (L : ℤ)).eval (x / (γ : ℂ)) /
        (Polynomial.Chebyshev.T ℂ (L : ℤ)).eval (1 / (γ : ℂ)) := by
  rw [specified_value_length L (Nat.pos_of_ne_zero (NeZero.ne L)),
    numerator_chebyshev hodd hγ hγ1, denominatorProduct_chebyshev hodd hγ hγ1]
  simp only [eval_mul, eval_C, eval_comp, eval_X]
  rw [mul_comm ((γ : ℂ)⁻¹) x, ← div_eq_mul_inv]
  exact mul_div_mul_left _ _ (pow_ne_zero L (by exact_mod_cast hγ.ne'))

/-- The same identity for the complete odd schedule, valid for every complex input. -/
theorem terminal_value_chebyshev (ℓ : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℂ) :
    PhaseRecurrence.value x (terminalPhases ℓ γ) =
      (Polynomial.Chebyshev.T ℂ ((2 * ℓ + 1 : ℕ) : ℤ)).eval (x / (γ : ℂ)) /
        (Polynomial.Chebyshev.T ℂ ((2 * ℓ + 1 : ℕ) : ℤ)).eval (1 / (γ : ℂ)) := by
  have hodd : Odd (2 * ℓ + 1) := ⟨ℓ, by omega⟩
  simpa only [terminalPhases, Nat.add_sub_cancel] using
    specified_value_chebyshev hodd hγ hγ1 x

/-- Real inputs agree with the signed scalar amplitude from M11. -/
theorem specified_value_eq_amplitude {L : ℕ} [NeZero L] (hodd : Odd L)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℝ) :
    PhaseRecurrence.value (x : ℂ) (specifiedPrefix L γ (L - 1)) =
      (QFixLean.Chebyshev.amplitude L γ x : ℂ) := by
  rw [specified_value_chebyshev hodd hγ hγ1]
  simp only [QFixLean.Chebyshev.amplitude, QFixLean.Chebyshev.denominator,
    QFixLean.Chebyshev.evalT, Complex.ofReal_div,
    Polynomial.Chebyshev.complex_ofReal_eval_T, Complex.ofReal_one]

theorem terminal_value_eq_amplitude (ℓ : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℝ) :
    PhaseRecurrence.value (x : ℂ) (terminalPhases ℓ γ) =
      (QFixLean.Chebyshev.amplitude (2 * ℓ + 1) γ x : ℂ) := by
  have hodd : Odd (2 * ℓ + 1) := ⟨ℓ, by omega⟩
  simpa only [terminalPhases, Nat.add_sub_cancel] using
    specified_value_eq_amplitude hodd hγ hγ1 x

/-- Modulus squared retains the sign-sensitive amplitude identity above. -/
theorem terminal_value_norm_sq (ℓ : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (x : ℝ) :
    ‖PhaseRecurrence.value (x : ℂ) (terminalPhases ℓ γ)‖ ^ 2 =
      (QFixLean.Chebyshev.amplitude (2 * ℓ + 1) γ x) ^ 2 := by
  rw [terminal_value_eq_amplitude ℓ hγ hγ1 x, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

end
end QFixLean.QuasiChebyshev
