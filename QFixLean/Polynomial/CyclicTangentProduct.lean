module

public import QFixLean.Polynomial.CyclicTangent
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The product of the nonzero cyclic tangent factors

P24, arXiv:2403.02057v3, §4.2.3, HTML Lemma 4.13 / PDF Lemma 9:
this supplies the second base case of the downward induction. The proof
identifies the monic root polynomial and extracts its coefficient of `X`.
The polynomial has odd powers; the imaginary-part parity and cosine-factor
directions in the paper's intermediate Euler expansion are corrected here.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section
open Polynomial

private theorem tangent_pow_eq {L n : ℕ} {x : ℝ} (hc : Real.cos x ≠ 0)
    (hx : (L : ℝ) * x = (n : ℝ) * Real.pi) :
    (1 + Complex.I * (Real.tan x : ℂ)) ^ L =
      (1 - Complex.I * (Real.tan x : ℂ)) ^ L := by
  have hcC : (Real.cos x : ℂ) ≠ 0 := by exact_mod_cast hc
  have hp : (Real.cos x : ℂ) * (1 + Complex.I * (Real.tan x : ℂ)) =
      Complex.cos (x : ℂ) + Complex.sin (x : ℂ) * Complex.I := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp [hcC]
  have hm : (Real.cos x : ℂ) * (1 - Complex.I * (Real.tan x : ℂ)) =
      Complex.cos (- (x : ℂ)) + Complex.sin (- (x : ℂ)) * Complex.I := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp [hcC]
    ring
  have hpx : (L : ℂ) * (x : ℂ) = ((n : ℝ) * Real.pi : ℝ) := by exact_mod_cast hx
  have hmx : (L : ℂ) * (-(x : ℂ)) = -(((n : ℝ) * Real.pi : ℝ) : ℂ) := by rw [mul_neg, hpx]
  have hpL := congrArg (fun z : ℂ => z ^ L) hp
  have hmL := congrArg (fun z : ℂ => z ^ L) hm
  rw [mul_pow, Complex.cos_add_sin_mul_I_pow, hpx] at hpL
  rw [mul_pow, Complex.cos_add_sin_mul_I_pow, hmx] at hmL
  have hsin : Complex.sin (((n : ℝ) * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin, Real.sin_nat_mul_pi, Complex.ofReal_zero]
  simp only [hsin, zero_mul, add_zero] at hpL
  simp only [Complex.cos_neg, Complex.sin_neg, hsin, neg_zero, zero_mul, add_zero] at hmL
  exact mul_left_cancel₀ (pow_ne_zero L hcC) (hpL.trans hmL.symm)

/-- The binomial polynomial used to identify tangent roots at odd cycle lengths. -/
def cyclicRootPolynomial (L : ℕ) : Polynomial ℂ :=
  C (1 / 2) * ((X + 1) ^ L + (X - 1) ^ L)

private theorem coeff_X_sub_one_pow (n k : ℕ) :
    (((X : Polynomial ℂ) - 1) ^ n).coeff k = (-1 : ℂ) ^ (n - k) * (n.choose k : ℂ) := by
  simpa only [map_neg, map_one, sub_eq_add_neg] using
    (coeff_X_add_C_pow (-1 : ℂ) n k)

private theorem cyclicRootPolynomial_degree (L : ℕ) : (cyclicRootPolynomial L).natDegree ≤ L := by
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_add_le _ _).trans
  simp only [natDegree_pow, ← C_1, natDegree_X_add_C, natDegree_X_sub_C, mul_one,
    max_self, le_refl]

private theorem cyclicRootPolynomial_monic (L : ℕ) : (cyclicRootPolynomial L).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one L (cyclicRootPolynomial_degree L)
  norm_num [cyclicRootPolynomial, coeff_X_add_one_pow, coeff_X_sub_one_pow]

private theorem cyclicRootPolynomial_coeff_one {L : ℕ} (hodd : Odd L) :
    (cyclicRootPolynomial L).coeff 1 = (L : ℂ) := by
  have heven : Even (L - 1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  simp only [cyclicRootPolynomial, coeff_C_mul, coeff_add, coeff_X_add_one_pow,
    coeff_X_sub_one_pow, Nat.choose_one_right, heven.neg_one_pow, one_mul]
  ring

private theorem cyclicRootPolynomial_eval {L : ℕ} (hodd : Odd L) {z : ℂ}
    (hz : (1 + z) ^ L = (1 - z) ^ L) : (cyclicRootPolynomial L).IsRoot z := by
  change (cyclicRootPolynomial L).eval z = 0
  have hneg : z - 1 = -(1 - z) := by ring
  simp only [cyclicRootPolynomial, eval_mul, eval_C, eval_add, eval_pow, eval_X,
    eval_one, eval_sub, hneg, hodd.neg_pow]
  rw [add_comm z 1, hz]
  ring

private theorem product_roots {L : ℕ} [NeZero L] (hodd : Odd L) (z : ZMod L → ℂ)
    (hinj : Function.Injective z) (hz : ∀ r, (1 + z r) ^ L = (1 - z r) ^ L) :
    (∏ r : ZMod L, (X - C (z r))) = cyclicRootPolynomial L := by
  apply Eq.symm
  apply eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C z Finset.univ) (cyclicRootPolynomial_monic L)
  · apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
    intro r
    exact dvd_iff_isRoot.mpr (cyclicRootPolynomial_eval hodd (hz r))
  · simpa only [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
      ZMod.card] using cyclicRootPolynomial_degree L

private theorem prod_erase_zero {L : ℕ} [NeZero L] (hodd : Odd L) (z : ZMod L → ℂ)
    (hinj : Function.Injective z) (hz0 : z 0 = 0)
    (hz : ∀ r, (1 + z r) ^ L = (1 - z r) ^ L) :
    (∏ r ∈ (Finset.univ : Finset (ZMod L)).erase 0, z r) = (L : ℂ) := by
  classical
  have hroot := product_roots hodd z hinj hz
  have hprod := Finset.prod_erase_mul (Finset.univ : Finset (ZMod L))
    (fun r => (X - C (z r) : Polynomial ℂ)) (Finset.mem_univ (0 : ZMod L))
  rw [hz0, map_zero, sub_zero] at hprod
  rw [← hprod] at hroot
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 1) hroot
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X] at hcoeff
  simp only [coeff_zero_prod, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at hcoeff
  rw [Finset.prod_neg, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod L)),
    Finset.card_univ, ZMod.card] at hcoeff
  have heven : Even (L - 1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  rw [heven.neg_one_pow, one_mul, cyclicRootPolynomial_coeff_one hodd] at hcoeff
  exact hcoeff

/-- The two binomial powers agree because the multiplied angle is an integral
multiple of π. This uses actual trigonometric values and pole avoidance. -/
theorem cyclicZ_one_add_pow_eq_one_sub_pow {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (r : ZMod L) :
    (1 + cyclicZ L r) ^ L = (1 - cyclicZ L r) ^ L := by
  apply tangent_pow_eq (n := r.val) (cyclic_cos_ne_zero hL hodd r)
  unfold cyclicArgument
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp [hLr]

/-- The complete root polynomial of the imaginary tangent factors on an odd
cycle. Neither root multiplicities nor polynomial normalization are assumed. -/
theorem cyclicZ_rootPolynomial {L : ℕ} [NeZero L] (hodd : Odd L) :
    (∏ r : ZMod L, (X - C (cyclicZ L r))) = cyclicRootPolynomial L := by
  exact product_roots hodd (cyclicZ L)
    (cyclicZ_injective (NeZero.pos L) hodd)
    (cyclicZ_one_add_pow_eq_one_sub_pow (NeZero.pos L) hodd)

/-- The product over all nonzero indices is the cycle length, also for `L=1`
where this is an empty product. -/
theorem cyclicZ_prod_erase_zero {L : ℕ} [NeZero L] (hodd : Odd L) :
    (∏ r ∈ (Finset.univ : Finset (ZMod L)).erase 0, cyclicZ L r) = (L : ℂ) := by
  exact prod_erase_zero hodd (cyclicZ L)
    (cyclicZ_injective (NeZero.pos L) hodd) (cyclicZ_zero L)
    (cyclicZ_one_add_pow_eq_one_sub_pow (NeZero.pos L) hodd)

end
end QFixLean.QuasiChebyshev
