module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite cyclic product sums

The algebraic downward induction used in P24 v3, PDF Lemma 9
(HTML Lemma 4.13), separated from the tangent identities. Every element
of the finite additive group is counted as a translation parameter.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Sum over all translation parameters, including repeated translated sets. -/
def cyclicProductSum (z : G → ℂ) (S : Finset G) : ℂ :=
  ∑ j, ∏ m ∈ S, z (m + j)

omit [DecidableEq G] in
@[simp] theorem cyclicProductSum_empty (z : G → ℂ) :
    cyclicProductSum z ∅ = (Fintype.card G : ℂ) := by
  simp [cyclicProductSum]

/-- Translating the index set only permutes the translation parameters. -/
theorem cyclicProductSum_translate (z : G → ℂ) (S : Finset G) (a : G) :
    cyclicProductSum z (S.image (· + a)) = cyclicProductSum z S := by
  unfold cyclicProductSum
  simp_rw [Finset.prod_image (fun _ _ _ _ h => add_right_cancel h), add_assoc]
  exact Equiv.sum_comp (Equiv.addLeft a) (fun j => ∏ m ∈ S, z (m + j))

omit [DecidableEq G] in
theorem cyclicProductSum_univ (z : G → ℂ) (hz : z 0 = 0) :
    cyclicProductSum z Finset.univ = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact Finset.prod_eq_zero (Finset.mem_univ (-j)) (by simpa using hz)

/-- Of the translated complements of one point, only the one omitting zero
can have a nonzero product. This does not use the downward induction. -/
theorem cyclicProductSum_erase (z : G → ℂ) (hz : z 0 = 0) (a : G) :
    cyclicProductSum z (Finset.univ.erase a) =
      ∏ r ∈ Finset.univ.erase (0 : G), z r := by
  unfold cyclicProductSum
  rw [Finset.sum_eq_single (-a)]
  · apply Finset.prod_bij (fun m _ => m - a)
    · intro m hm
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm ⊢
      exact sub_ne_zero.mpr hm
    · intro m _ n _ h
      exact sub_left_injective h
    · intro r hr
      refine ⟨r + a, ?_, by simp⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      exact (Finset.mem_erase.mp hr).1 (add_right_cancel (h.trans (zero_add a).symm))
    · intro m _
      simp only [sub_eq_add_neg]
  · intro j _ hj
    apply Finset.prod_eq_zero (i := -j)
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      exact hj (by simpa using congrArg Neg.neg h)
    · simpa using hz
  · simp

/-- The two inserted indices are genuinely new; the difference identity
is applied term by term before taking the finite sum. -/
theorem cyclicProductSum_insert_sub (z : G → ℂ)
    (hdiff : ∀ a b j, z (b + j) - z (a + j) =
      z (b - a) * (1 - z (b + j) * z (a + j)))
    (S : Finset G) {a b : G} (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    cyclicProductSum z (insert b S) - cyclicProductSum z (insert a S) =
      z (b - a) * (cyclicProductSum z S - cyclicProductSum z (insert a (insert b S))) := by
  unfold cyclicProductSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.prod_insert ha, Finset.prod_insert hb,
    Finset.prod_insert (show a ∉ insert b S by simp [ha, hab])]
  calc
    _ = (z (b + j) - z (a + j)) * (∏ m ∈ S, z (m + j)) := by ring
    _ = _ := by rw [hdiff]; ring

/-- The finite-set induction behind the cyclic tangent identity. The analytic
hypotheses are established separately for the actual, unscaled tangent. -/
theorem cyclicProductSum_eq_of_identities (z : G → ℂ)
    (hodd : Odd (Fintype.card G)) (hz : z 0 = 0)
    (hnz : ∀ r, r ≠ 0 → z r ≠ 0)
    (hdiff : ∀ a b j, z (b + j) - z (a + j) =
      z (b - a) * (1 - z (b + j) * z (a + j)))
    (hprod : (∏ r ∈ Finset.univ.erase (0 : G), z r) = (Fintype.card G : ℂ))
    (S : Finset G) :
    cyclicProductSum z S = if Even S.card then (Fintype.card G : ℂ) else 0 := by
  generalize hn : Sᶜ.card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hzero : n = 0
    · have hc : Sᶜ = ∅ := Finset.card_eq_zero.mp (hn.trans hzero)
      have hS : S = Finset.univ := by
        ext x
        have hx := Finset.ext_iff.mp hc x
        simpa using hx
      simp [hS, cyclicProductSum_univ z hz, Nat.not_even_iff_odd.mpr hodd]
    by_cases hone : n = 1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hn.trans hone)
      have hS : S = Finset.univ.erase a := by
        ext x
        have hx := Finset.ext_iff.mp ha x
        simpa using not_congr hx
      have heven : Even (Fintype.card G - 1) := by
        obtain ⟨k, hk⟩ := hodd
        refine ⟨k, ?_⟩
        omega
      simp only [hS, cyclicProductSum_erase z hz, hprod,
        Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
      simp [heven]
    have htwo : 1 < Sᶜ.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    simp only [Finset.mem_compl] at ha hb
    have habs : a ∉ insert b S := by simp [ha, hab]
    have hcard := Finset.card_le_univ S
    have hia : (insert a S)ᶜ.card < n := by
      rw [Finset.card_compl, Finset.card_insert_of_notMem ha]
      rw [Finset.card_compl] at hn
      omega
    have hib : (insert b S)ᶜ.card < n := by
      rw [Finset.card_compl, Finset.card_insert_of_notMem hb]
      rw [Finset.card_compl] at hn
      omega
    have hiab : (insert a (insert b S))ᶜ.card < n := by
      rw [Finset.card_compl, Finset.card_insert_of_notMem habs,
        Finset.card_insert_of_notMem hb]
      rw [Finset.card_compl] at hn
      omega
    have h₁ := ih _ hia (insert a S) rfl
    have h₂ := ih _ hib (insert b S) rfl
    have h₃ := ih _ hiab (insert a (insert b S)) rfl
    have heq : cyclicProductSum z (insert b S) = cyclicProductSum z (insert a S) := by
      rw [Finset.card_insert_of_notMem ha] at h₁
      rw [Finset.card_insert_of_notMem hb] at h₂
      exact h₂.trans h₁.symm
    have hbridge := cyclicProductSum_insert_sub z hdiff S ha hb hab
    rw [heq, sub_self] at hbridge
    have hsame : cyclicProductSum z S = cyclicProductSum z (insert a (insert b S)) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hbridge.symm).resolve_left
        (hnz (b - a) (sub_ne_zero.mpr hab.symm)))
    rw [hsame, h₃, Finset.card_insert_of_notMem habs,
      Finset.card_insert_of_notMem hb]
    simp only [Nat.even_add_one, not_not]

omit [DecidableEq G] in
/-- Coefficients may depend on the original index, but not on the shift. -/
theorem cyclicProductSum_fixed_coefficients (z c : G → ℂ) (S : Finset G) :
    (∑ j, ∏ m ∈ S, c m * z (m + j)) =
      (∏ m ∈ S, c m) * cyclicProductSum z S := by
  simp only [Finset.prod_mul_distrib, cyclicProductSum, Finset.mul_sum]

omit [DecidableEq G] in
/-- A constant scale contributes one factor for each index, including the
empty product when the scale is zero. -/
theorem cyclicProductSum_scale (z : G → ℂ) (S : Finset G) (c : ℂ) :
    cyclicProductSum (fun r => c * z r) S = c ^ S.card * cyclicProductSum z S := by
  simpa only [cyclicProductSum, Finset.prod_const] using
    cyclicProductSum_fixed_coefficients z (fun _ => c) S

/-- An injective finite enumeration retains every factor exactly once. -/
theorem cyclicProductSum_image {K : Type*} [Fintype K]
    (z : G → ℂ) (f : K → G) (hf : Function.Injective f) :
    cyclicProductSum z (Finset.univ.image f) = ∑ j, ∏ m, z (f m + j) := by
  unfold cyclicProductSum
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.prod_image (fun _ _ _ _ h => hf h)

end
end QFixLean.QuasiChebyshev
