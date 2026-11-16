module

public import QFixLean.Polynomial.CyclicTangentSum
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Rotation averages of products with distinct endpoints

An exact finite-subset expansion applies the M15 cyclic tangent sum to
all subsets of distinct endpoints. All rotation parameters are retained;
no assumption about sizes of rotation orbits is used.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open scoped BigOperators

/-- M15 transported along an injective finite endpoint enumeration. -/
theorem cyclicZ_sum_prod_endpoints {L : ℕ} [NeZero L] (hodd : Odd L)
    {α : Type*} (S : Finset α) (f : α → ZMod L) (hf : Set.InjOn f S)
    (c : α → ℂ) :
    (∑ j : ZMod L, ∏ a ∈ S, c a * cyclicZ L (f a + j)) =
      (∏ a ∈ S, c a) * (if Even S.card then (L : ℂ) else 0) := by
  classical
  simp_rw [Finset.prod_mul_distrib]
  rw [← Finset.mul_sum]
  congr 1
  have h := cyclicTangentSum_eq hodd (S.image f)
  simpa only [cyclicTangentSum, cyclicProductSum, Finset.prod_image hf,
    Finset.card_image_of_injOn hf] using h

/-- Full product expansion, with the parity of every selected subset kept.
The endpoints are distinct before M15 is applied. -/
theorem cyclicZ_product_average {L : ℕ} [NeZero L] (hodd : Odd L)
    {α : Type*} (S : Finset α) (f : α → ZMod L) (hf : Set.InjOn f S)
    (c : α → ℂ) :
    (∑ j : ZMod L, ∏ a ∈ S, (1 + c a * cyclicZ L (f a + j))) =
      (L : ℂ) / 2 * ((∏ a ∈ S, (1 + c a)) + (∏ a ∈ S, (1 - c a))) := by
  classical
  simp_rw [Finset.prod_one_add]
  simp_rw [sub_eq_add_neg, Finset.prod_one_add]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hAS : A ⊆ S := Finset.mem_powerset.mp hA
  rw [cyclicZ_sum_prod_endpoints hodd A f (hf.mono hAS) c, Finset.prod_neg]
  rcases Nat.even_or_odd A.card with he | ho
  · rw [ite_eq_left he, he.neg_one_pow]
    ring
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow]
    ring

/-- The polynomial version proves every coefficient at once by exact
finite-product identities, including the constant and out-of-range terms. -/
theorem cyclicZ_polynomial_average {L : ℕ} [NeZero L] (hodd : Odd L)
    {α : Type*} (S : Finset α) (f : α → ZMod L) (hf : Set.InjOn f S)
    (c : α → ℂ) :
    (∑ j : ZMod L, ∏ a ∈ S,
      (1 + Polynomial.C (c a * cyclicZ L (f a + j)) * Polynomial.X)) =
      Polynomial.C ((L : ℂ) / 2) *
        ((∏ a ∈ S, (1 + Polynomial.C (c a) * Polynomial.X)) +
         (∏ a ∈ S, (1 - Polynomial.C (c a) * Polynomial.X))) := by
  classical
  apply Polynomial.funext
  intro y
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_sub]
  convert cyclicZ_product_average hodd S f hf (fun a => c a * y) using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro a _
  ring

end
end QFixLean.QuasiChebyshev
