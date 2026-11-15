module

public import QFixLean.Polynomial.CyclicProductSum
public import QFixLean.Polynomial.CyclicTangentProduct
import Mathlib.Tactic.Ring

/-!
# The cyclic tangent product-sum identity

P24 v3, PDF Lemma 9 / equation (53), HTML Lemma 4.13 / equation (54).
For every subset of an odd cycle, the sum over all translation parameters
is its cycle length for even cardinality and zero for odd cardinality.
The empty subset and length one are included. No primeness or full-length
orbit hypothesis is used. The quasi-Chebyshev identity remains separate.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open scoped BigOperators

/-- The actual unscaled tangent factors, summed over all `L` shifts. -/
def cyclicTangentSum (L : ℕ) [NeZero L] (S : Finset (ZMod L)) : ℂ :=
  cyclicProductSum (cyclicZ L) S

@[simp] theorem cyclicTangentSum_empty (L : ℕ) [NeZero L] :
    cyclicTangentSum L ∅ = (L : ℂ) := by
  simp [cyclicTangentSum, ZMod.card]

theorem cyclicTangentSum_translate (L : ℕ) [NeZero L]
    (S : Finset (ZMod L)) (a : ZMod L) :
    cyclicTangentSum L (S.image (· + a)) = cyclicTangentSum L S :=
  cyclicProductSum_translate _ _ _

theorem cyclicTangentSum_univ (L : ℕ) [NeZero L] :
    cyclicTangentSum L Finset.univ = 0 :=
  cyclicProductSum_univ _ (cyclicZ_zero L)

/-- The second induction base is proved from the independent root polynomial. -/
theorem cyclicTangentSum_erase {L : ℕ} [NeZero L] (hodd : Odd L) (a : ZMod L) :
    cyclicTangentSum L (Finset.univ.erase a) = (L : ℂ) := by
  rw [cyclicTangentSum, cyclicProductSum_erase _ (cyclicZ_zero L)]
  exact cyclicZ_prod_erase_zero hodd

theorem cyclicTangentSum_insert_sub {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) {a b : ZMod L}
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    cyclicTangentSum L (insert b S) - cyclicTangentSum L (insert a S) =
      cyclicZ L (b - a) *
        (cyclicTangentSum L S - cyclicTangentSum L (insert a (insert b S))) :=
  cyclicProductSum_insert_sub _ (cyclicZ_sub_identity (NeZero.pos L) hodd) S ha hb hab

/-- The general cyclic tangent identity, with no unproved analytic premises. -/
theorem cyclicTangentSum_eq {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) :
    cyclicTangentSum L S = if Even S.card then (L : ℂ) else 0 := by
  simpa only [cyclicTangentSum, ZMod.card] using
    cyclicProductSum_eq_of_identities (cyclicZ L)
    (by simpa only [ZMod.card] using hodd) (cyclicZ_zero L)
    (fun r hr => fun hz => hr ((cyclicZ_eq_zero_iff (NeZero.pos L) hodd r).mp hz))
    (cyclicZ_sub_identity (NeZero.pos L) hodd)
    (by simpa only [ZMod.card] using cyclicZ_prod_erase_zero hodd) S

theorem cyclicTangentSum_even {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) (hS : Even S.card) : cyclicTangentSum L S = (L : ℂ) := by
  simp [cyclicTangentSum_eq hodd S, hS]

theorem cyclicTangentSum_odd {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) (hS : Odd S.card) : cyclicTangentSum L S = 0 := by
  simp [cyclicTangentSum_eq hodd S, Nat.not_even_iff_odd.mpr hS]

@[simp] theorem cyclicTangentSum_singleton {L : ℕ} [NeZero L]
    (hodd : Odd L) (a : ZMod L) : cyclicTangentSum L {a} = 0 := by
  simp [cyclicTangentSum_eq hodd]

/-- An injective enumeration is equivalent to a set of distinct modular indices. -/
theorem cyclicTangentSum_injective {L k : ℕ} [NeZero L] (hodd : Odd L)
    (f : Fin k → ZMod L) (hf : Function.Injective f) :
    (∑ j : ZMod L, ∏ m : Fin k, cyclicZ L (f m + j)) =
      if Even k then (L : ℂ) else 0 := by
  rw [← cyclicProductSum_image _ f hf]
  have h := cyclicTangentSum_eq hodd (Finset.univ.image f)
  simpa only [cyclicTangentSum, Finset.card_image_of_injective _ hf,
    Finset.card_univ, Fintype.card_fin] using h

/-- Fixed weights are attached to the original indices, independently of the shift. -/
theorem cyclicTangentSum_fixed_coefficients {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) (c : ZMod L → ℂ) :
    (∑ j : ZMod L, ∏ m ∈ S, c m * cyclicZ L (m + j)) =
      (∏ m ∈ S, c m) * (if Even S.card then (L : ℂ) else 0) := by
  rw [cyclicProductSum_fixed_coefficients]
  change (∏ m ∈ S, c m) * cyclicTangentSum L S = _
  rw [cyclicTangentSum_eq hodd]

/-- Scaling is algebraic and valid for every real `w`; it never requires `w ≠ 0`. -/
theorem cyclicTangentSum_scaled {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) (w : ℝ) :
    (∑ j : ZMod L, ∏ m ∈ S,
      Complex.I * ((w * cyclicTangent L (m + j) : ℝ) : ℂ)) =
      (w : ℂ) ^ S.card * (if Even S.card then (L : ℂ) else 0) := by
  have hf : (fun r => Complex.I * ((w * cyclicTangent L r : ℝ) : ℂ)) =
      (fun r => (w : ℂ) * cyclicZ L r) := by
    funext r
    simp only [Complex.ofReal_mul, cyclicZ]
    ring
  change cyclicProductSum (fun r => Complex.I * ((w * cyclicTangent L r : ℝ) : ℂ)) S = _
  rw [hf, cyclicProductSum_scale]
  change (w : ℂ) ^ S.card * cyclicTangentSum L S = _
  rw [cyclicTangentSum_eq hodd]

/-- The same theorem stated with the M14 phase tangents at modular representatives. -/
theorem cyclicTangentSum_phase_tangent {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) (γ : ℝ) :
    (∑ j : ZMod L, ∏ m ∈ S, Complex.I * (tangent L γ (m + j).val : ℂ)) =
      (Real.sqrt (1 - γ ^ 2) : ℂ) ^ S.card *
        (if Even S.card then (L : ℂ) else 0) := by
  simpa only [tangent_val_eq_scaled_cyclic] using
    cyclicTangentSum_scaled hodd S (Real.sqrt (1 - γ ^ 2))

/-- At `γ = 1`, the empty product still contributes one for every shift. -/
theorem cyclicTangentSum_phase_gamma_one {L : ℕ} [NeZero L] (hodd : Odd L)
    (S : Finset (ZMod L)) :
    (∑ j : ZMod L, ∏ m ∈ S, Complex.I * (tangent L 1 (m + j).val : ℂ)) =
      if S = ∅ then (L : ℂ) else 0 := by
  rw [cyclicTangentSum_phase_tangent hodd]
  by_cases hS : S = ∅
  · simp [hS]
  · simp [hS, Finset.card_eq_zero.not.mpr hS]

end
end QFixLean.QuasiChebyshev
