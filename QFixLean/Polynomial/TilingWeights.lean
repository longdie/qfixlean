module

public import QFixLean.Polynomial.RotationProducts
public import QFixLean.Polynomial.CyclicTilings
import Mathlib.Tactic.Ring

/-!
# Cyclic tiling weight comparison

The complete sum over `L` rotations is retained even for periodic tilings.
A double sum over the permutation of all legal tilings handles every
rotation multiplicity, without choosing orbit representatives.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open scoped BigOperators
open Polynomial

/-- The product of the two signed tangent factors for each domino. -/
def tilingFactor {L : ℕ} [NeZero L] (D : Finset (ZMod L)) (y : ℂ) : ℂ :=
  ∏ n ∈ D, (1 - cyclicZ L n * y) * (1 + cyclicZ L (n - 1) * y)

/-- The same factor as a polynomial in the independent scaling variable. -/
def tilingFactorPolynomial {L : ℕ} [NeZero L]
    (D : Finset (ZMod L)) : Polynomial ℂ :=
  ∏ n ∈ D, (1 - C (cyclicZ L n) * X) * (1 + C (cyclicZ L (n - 1)) * X)

@[simp] theorem tilingFactorPolynomial_eval {L : ℕ} [NeZero L]
    (D : Finset (ZMod L)) (y : ℂ) :
    (tilingFactorPolynomial D).eval y = tilingFactor D y := by
  simp [tilingFactorPolynomial, tilingFactor, eval_prod]

/-- Reflection of sites negates and exchanges the two endpoints; the domino
index is `1-n`, so the two signed factors are preserved in reverse order. -/
theorem tangent_domino_reflection {L : ℕ} [NeZero L] (n : ZMod L) (y : ℂ) :
    (1 - cyclicZ L (1 - n) * y) * (1 + cyclicZ L (1 - n - 1) * y) =
      (1 - cyclicZ L n * y) * (1 + cyclicZ L (n - 1) * y) := by
  have he : 1 - n = -(n - 1) := by abel
  have hf : 1 - n - 1 = -n := by abel
  rw [hf, he, cyclicZ_neg (NeZero.pos L), cyclicZ_neg (NeZero.pos L)]
  ring

/-- The reflection used in the line-to-cycle correspondence preserves weight. -/
theorem tilingFactor_reflect {L : ℕ} [NeZero L]
    (D : Finset (ZMod L)) (y : ℂ) :
    tilingFactor (reflectTilings D) y = tilingFactor D y := by
  rw [tilingFactor, reflectTilings,
    Finset.prod_image (fun _ _ _ _ h => sub_right_injective h)]
  apply Finset.prod_congr rfl
  intro n _
  exact tangent_domino_reflection n y

/-- Sum over all rotations for one fixed legal tiling. Repeated rotated
objects remain repeated terms of the sum. -/
theorem tilingFactor_rotation_sum {L : ℕ} [NeZero L] (hodd : Odd L)
    (D : Finset (ZMod L)) (hD : IsCyclicTiling D) (y : ℂ) :
    (∑ j : ZMod L, tilingFactor (rotateTilings j D) y) =
      (L : ℂ) * (1 - y ^ 2) ^ D.card := by
  classical
  have h := cyclicZ_product_average hodd
    (Finset.univ : Finset ({n // n ∈ D} × Bool))
    (fun p => dominoEndpoint p.1.val p.2) hD.endpoint_injective.injOn
    (fun p => if p.2 then y else -y)
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, dominoEndpoint,
    Bool.false_eq_true, ↓reduceIte, Finset.univ_eq_attach] at h
  simp only [Finset.prod_const, Finset.card_attach] at h
  have hplus : (1 + y) * (1 + -y) = 1 - y ^ 2 := by ring
  have hminus : (1 - y) * (1 - -y) = 1 - y ^ 2 := by ring
  rw [hplus, hminus] at h
  have hattach : ∀ j : ZMod L,
      (∏ n ∈ D.attach,
        (1 + y * cyclicZ L (n.val - 1 + j)) * (1 + -y * cyclicZ L (n.val + j))) =
      ∏ n ∈ D, (1 + y * cyclicZ L (n - 1 + j)) * (1 + -y * cyclicZ L (n + j)) := by
    intro j
    exact Finset.prod_attach D (fun n =>
      (1 + y * cyclicZ L (n - 1 + j)) * (1 + -y * cyclicZ L (n + j)))
  simp_rw [hattach] at h
  have hp : (∑ j : ZMod L, tilingFactor (rotateTilings j D) y) =
      ∑ j : ZMod L,
        ∏ n ∈ D, (1 + y * cyclicZ L (n - 1 + j)) * (1 + -y * cyclicZ L (n + j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [tilingFactor, rotateTilings, Finset.prod_image (fun _ _ _ _ e => add_right_cancel e)]
    apply Finset.prod_congr rfl
    intro n _
    have he : n + j - 1 = n - 1 + j := by abel
    rw [he]
    ring
  rw [hp, h]
  ring

/-- Polynomial equality, not just a bound or an equality of sampled values. -/
theorem tilingFactorPolynomial_rotation_sum {L : ℕ} [NeZero L] (hodd : Odd L)
    (D : Finset (ZMod L)) (hD : IsCyclicTiling D) :
    (∑ j : ZMod L, tilingFactorPolynomial (rotateTilings j D)) =
      C (L : ℂ) * (1 - X ^ 2) ^ D.card := by
  apply Polynomial.funext
  intro y
  simpa only [eval_finsetSum, tilingFactorPolynomial_eval, eval_mul, eval_C,
    eval_pow, eval_sub, eval_one, eval_X] using tilingFactor_rotation_sum hodd D hD y

/-- A fixed shift permutes the complete tiling type at each domino count. -/
theorem tilingFactor_sum_rotate {L : ℕ} [NeZero L] (d : ℕ) (j : ZMod L) (y : ℂ) :
    (∑ D : CyclicTilingCard L d, tilingFactor (rotateTilings j D.1) y) =
      ∑ D : CyclicTilingCard L d, tilingFactor D.1 y := by
  exact Equiv.sum_comp (rotateTilingCardEquiv j) (fun D => tilingFactor D.1 y)

/-- Double-sum correction of the orbit-size claim in P24. A periodic tiling
has a stabilizer; neither this equality nor its proof assumes a free action. -/
theorem tilingFactor_total_eq {L : ℕ} [NeZero L] (hodd : Odd L)
    (d : ℕ) (y : ℂ) :
    (∑ D : CyclicTilingCard L d, tilingFactor D.1 y) =
      ∑ _D : CyclicTilingCard L d, (1 - y ^ 2) ^ d := by
  have hdouble : (L : ℂ) * (∑ D : CyclicTilingCard L d, tilingFactor D.1 y) =
      (L : ℂ) * (∑ _D : CyclicTilingCard L d, (1 - y ^ 2) ^ d) := by
    calc
      _ = ∑ j : ZMod L, ∑ D : CyclicTilingCard L d, tilingFactor (rotateTilings j D.1) y := by
        simp only [tilingFactor_sum_rotate, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]
      _ = ∑ D : CyclicTilingCard L d, ∑ j : ZMod L, tilingFactor (rotateTilings j D.1) y :=
        Finset.sum_comm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _
        rw [tilingFactor_rotation_sum hodd D.1 D.2.1, D.2.2]
  exact mul_left_cancel₀ (by exact_mod_cast (NeZero.ne L)) hdouble

/-- The double-sum proof also works with an arbitrary cardinality-dependent
weight. This restores signs and singleton powers without orbit representatives. -/
theorem tilingFactor_weighted_total_eq {L : ℕ} [NeZero L] (hodd : Odd L)
    (a : ℕ → ℂ) (y : ℂ) :
    (∑ D : CyclicTiling L, a D.1.card * tilingFactor D.1 y) =
      ∑ D : CyclicTiling L, a D.1.card * (1 - y ^ 2) ^ D.1.card := by
  classical
  have hperm (j : ZMod L) :
      (∑ D : CyclicTiling L,
        a D.1.card * tilingFactor (rotateTilings j D.1) y) =
      ∑ D : CyclicTiling L, a D.1.card * tilingFactor D.1 y := by
    have ht := Equiv.sum_comp (rotateTilingEquiv j)
      (fun D : CyclicTiling L => a D.1.card * tilingFactor D.1 y)
    change (∑ D : CyclicTiling L,
      a (rotateTilings j D.1).card * tilingFactor (rotateTilings j D.1) y) = _ at ht
    simpa only [rotateTilings_card] using ht
  have hdouble : (L : ℂ) *
      (∑ D : CyclicTiling L, a D.1.card * tilingFactor D.1 y) =
      (L : ℂ) *
        (∑ D : CyclicTiling L, a D.1.card * (1 - y ^ 2) ^ D.1.card) := by
    calc
      _ = ∑ j : ZMod L, ∑ D : CyclicTiling L,
          a D.1.card * tilingFactor (rotateTilings j D.1) y := by
        simp only [hperm, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = ∑ D : CyclicTiling L, ∑ j : ZMod L,
          a D.1.card * tilingFactor (rotateTilings j D.1) y := Finset.sum_comm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D _
        rw [← Finset.mul_sum, tilingFactor_rotation_sum hodd D.1 D.2]
        ring
  exact mul_left_cancel₀ (by exact_mod_cast (NeZero.ne L)) hdouble

/-- Polynomial-valued cardinal weights are also supported, so singleton
powers and domino signs can be restored at the polynomial level. -/
theorem tilingFactor_polynomial_weighted_total_eq {L : ℕ} [NeZero L] (hodd : Odd L)
    (a : ℕ → Polynomial ℂ) (y : ℂ) :
    (∑ D : CyclicTiling L, a D.1.card * C (tilingFactor D.1 y)) =
      ∑ D : CyclicTiling L, a D.1.card * C ((1 - y ^ 2) ^ D.1.card) := by
  apply Polynomial.funext
  intro x
  simpa only [eval_finsetSum, eval_mul, eval_C] using
    tilingFactor_weighted_total_eq hodd (fun d => (a d).eval x) y

/-- Reinsert the negative sign of each domino and the common singleton
weight `(2X)^(L-2d)`. This is the full variable-weight versus constant-weight
cycle comparison used by the quasi-Chebyshev proof. -/
theorem cyclic_tiling_weight_comparison {L : ℕ} [NeZero L] (hodd : Odd L)
    (y : ℂ) :
    (∑ D : CyclicTiling L, (2 * (X : Polynomial ℂ)) ^ (L - 2 * D.1.card) *
      ∏ n ∈ D.1, -C ((1 - cyclicZ L n * y) * (1 + cyclicZ L (n - 1) * y))) =
    ∑ D : CyclicTiling L, (2 * (X : Polynomial ℂ)) ^ (L - 2 * D.1.card) *
      ∏ _n ∈ D.1, -C (1 - y ^ 2) := by
  classical
  have h := tilingFactor_polynomial_weighted_total_eq hodd
    (fun d => (2 * (X : Polynomial ℂ)) ^ (L - 2 * d) * (-1) ^ d) y
  convert h using 1 <;>
    apply Finset.sum_congr rfl <;> intro D _
  · simp only [tilingFactor, Finset.prod_neg, ← map_prod]
    ring
  · simp only [Finset.prod_const]
    rw [neg_pow, map_pow]
    ring

end
end QFixLean.QuasiChebyshev
