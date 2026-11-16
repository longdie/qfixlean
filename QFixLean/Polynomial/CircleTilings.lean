module

public import QFixLean.Polynomial.CyclicTilings
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Circle weights and the modified cut

At site zero, a cyclic tiling has precisely three possibilities: a single,
domino one, or domino zero. Reflection interchanges the two domino cases.
The cut deletes the domino-zero case and halves the single-zero case.
Thus its total is half the full circle total, including periodic tilings.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial
open scoped BigOperators

/-- The product of uniform singleton weights and individual domino weights.
Legality ensures that `L - 2*D.card` is exactly the number of singletons. -/
def cyclicWeight {L : ℕ} {R : Type*} [CommSemiring R]
    (x : R) (b : ZMod L → R) (D : Finset (ZMod L)) : R :=
  (2 * x) ^ (L - 2 * D.card) * ∏ n ∈ D, b n

/-- The modified cut has no wraparound domino, and a site-zero single has
weight `x` instead of `2*x`. -/
def cutWeight {L : ℕ} (W : CyclicTiling L → Polynomial ℂ)
    (D : CyclicTiling L) : Polynomial ℂ :=
  if 0 ∈ D.val then 0 else if 1 ∈ D.val then W D else C (1 / 2 : ℂ) * W D

@[simp] theorem zero_mem_reflectTilings {L : ℕ} (D : Finset (ZMod L)) :
    0 ∈ reflectTilings D ↔ 1 ∈ D := by
  simp only [reflectTilings, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, h⟩
    have : n = 1 := by linear_combination -h
    simpa [this] using hn
  · intro h
    exact ⟨1, h, by simp⟩

@[simp] theorem one_mem_reflectTilings {L : ℕ} (D : Finset (ZMod L)) :
    1 ∈ reflectTilings D ↔ 0 ∈ D := by
  simp only [reflectTilings, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, h⟩
    have : n = 0 := by linear_combination -h
    simpa [this] using hn
  · intro h
    exact ⟨0, h, by simp⟩

/-- Uniform singleton weights and reflection-invariant domino weights give
exactly equal reflected products. -/
theorem cyclicWeight_reflect {L : ℕ} {R : Type*} [CommSemiring R]
    (x : R) (b : ZMod L → R) (hb : ∀ n, b (1 - n) = b n)
    (D : Finset (ZMod L)) :
    cyclicWeight x b (reflectTilings D) = cyclicWeight x b D := by
  rw [cyclicWeight, reflectTilings_card, cyclicWeight]
  congr 1
  rw [reflectTilings, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun n _ => hb n)
  · intro n _ m _ h
    exact sub_right_injective h

/-- Pairwise comparison uses the actual three site-zero cases. -/
theorem weight_add_reflect_eq_twice_cut {L : ℕ}
    (W : CyclicTiling L → Polynomial ℂ)
    (hW : ∀ D, W (reflectTilingEquiv D) = W D) (D : CyclicTiling L) :
    W D + W (reflectTilingEquiv D) =
      2 * (cutWeight W D + cutWeight W (reflectTilingEquiv D)) := by
  have h0 : 0 ∈ (reflectTilingEquiv D).val ↔ 1 ∈ D.val := zero_mem_reflectTilings _
  have h1 : 1 ∈ (reflectTilingEquiv D).val ↔ 0 ∈ D.val := one_mem_reflectTilings _
  simp only [cutWeight, hW, h0, h1]
  by_cases hD0 : 0 ∈ D.val
  · have hD1 : 1 ∉ D.val := fun h => D.property.not_zero_and_one ⟨hD0, h⟩
    simp [hD0, hD1]
    ring
  · by_cases hD1 : 1 ∈ D.val
    · simp [hD0, hD1]
      ring
    · simp only [hD0, hD1, ↓reduceIte]
      have hh : (C (1 / 2 : ℂ) : Polynomial ℂ) + C (1 / 2 : ℂ) = 1 := by
        rw [← C_add]
        norm_num
      linear_combination -2 * W D * hh

/-- The full cycle sum is twice the modified line sum. The proof uses an
involutive permutation, so it never assumes full-length rotation orbits. -/
theorem sum_cyclicWeight_eq_twice_cut {L : ℕ} [NeZero L]
    (W : CyclicTiling L → Polynomial ℂ)
    (hW : ∀ D, W (reflectTilingEquiv D) = W D) :
    ∑ D, W D = 2 * ∑ D, cutWeight W D := by
  have h := congrArg (fun f : CyclicTiling L → Polynomial ℂ => ∑ D, f D)
    (funext (weight_add_reflect_eq_twice_cut W hW))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [Equiv.sum_comp reflectTilingEquiv W,
    Equiv.sum_comp reflectTilingEquiv (cutWeight W)] at h
  have h2 : (2 : Polynomial ℂ) ≠ 0 := by
    intro hz
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hz
    norm_num at this
  apply mul_left_cancel₀ h2
  linear_combination h

end
end QFixLean.QuasiChebyshev
