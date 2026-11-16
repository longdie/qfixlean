module

public import QFixLean.Polynomial.CircleTilings
public import QFixLean.Polynomial.CyclicTangent
public import QFixLean.Polynomial.LineTilings
public import QFixLean.Polynomial.ScaledChebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Matching the paper's phase weights with cyclic tiling weights

Domino `n` covers `n,n-1`. Reflection therefore sends its index to `1-n`.
The squared real scaling parameter is justified on `0 < γ ≤ 1`, including
the zero tangent scale at `γ=1`.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial

/-- The cyclic form of the original cleared-recurrence domino weight. -/
def cyclicPhaseDomino {L : ℕ} [NeZero L] (γ : ℝ) (n : ZMod L) : Polynomial ℂ :=
  -C ((1 - cyclicZ L n * (Real.sqrt (1 - γ ^ 2) : ℂ)) *
    (1 + cyclicZ L (n - 1) * (Real.sqrt (1 - γ ^ 2) : ℂ)))

/-- The two signs and the reversal of the two endpoint factors are exact. -/
theorem cyclicPhaseDomino_reflect {L : ℕ} [NeZero L] (γ : ℝ) (n : ZMod L) :
    cyclicPhaseDomino γ (1 - n) = cyclicPhaseDomino γ n := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  unfold cyclicPhaseDomino
  rw [show 1 - n - 1 = -n by ring, show 1 - n = -(n - 1) by ring,
    cyclicZ_neg hL, cyclicZ_neg hL]
  congr 1
  congr 1
  ring

/-- On a line there is no natural-number underflow at a domino endpoint. -/
theorem cyclicPhaseDomino_natCast {L : ℕ} [NeZero L] (γ : ℝ)
    (n : ℕ) (hn : 0 < n) :
    cyclicPhaseDomino γ (n : ZMod L) = LineTiling.phaseDomino (tangent L γ) n := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [cyclicPhaseDomino, LineTiling.phaseDomino,
    tangent_eq_scaled_cyclic hL, Complex.ofReal_mul, cyclicZ]
  rw [show (n : ZMod L) - 1 = ((n - 1 : ℕ) : ZMod L) by
    rw [Nat.cast_sub (by omega), Nat.cast_one]]
  congr 1
  congr 1
  ring

/-- The real square-root identity needs the scale's actual parameter domain. -/
theorem tangentScale_sq {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Real.sqrt (1 - γ ^ 2)) ^ 2 = 1 - γ ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem one_sub_complex_tangentScale_sq {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    1 - (Real.sqrt (1 - γ ^ 2) : ℂ) ^ 2 = (γ : ℂ) ^ 2 := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (tangentScale_sq hγ hγ1)
  push_cast at h
  linear_combination -h

/-- The finite constant-domino line sum has the scaled Chebyshev recurrence. -/
theorem line_total_constant (γ : ℂ) (n : ℕ) :
    LineTiling.total (LineTiling.modifiedSingleton X) (fun _ => -C (γ ^ 2)) n =
      scaledChebyshev γ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [LineTiling.modifiedSingleton]
  | more n ih₀ ih₁ =>
    rw [LineTiling.total_recurrence, ih₀, ih₁, scaledChebyshev_recurrence]
    simp only [LineTiling.modifiedSingleton, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte]
    ring

end
end QFixLean.QuasiChebyshev
