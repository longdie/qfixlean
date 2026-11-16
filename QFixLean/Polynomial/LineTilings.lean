module

public import QFixLean.Polynomial.QuasiChebyshevAlgebra
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Weighted tilings of a finite line

A layout is built by its rightmost tile, which is a singleton or an adjacent
pair. `dominoes` records the right endpoint of each pair. Its injectivity and
range characterization connect this finite layout type with actual disjoint
pairs on the line, rather than introducing a second scalar recurrence.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev.LineTiling

open scoped BigOperators
open Polynomial

/-- Actual layouts of the sites `0,…,n-1`, classified by their last tile. -/
@[reducible] def Layout : ℕ → Type
  | 0 => PUnit
  | 1 => PUnit
  | n + 2 => Layout (n + 1) ⊕ Layout n

instance instFintype : (n : ℕ) → Fintype (Layout n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | 1 => inferInstanceAs (Fintype PUnit)
  | n + 2 => by
    letI := instFintype (n + 1)
    letI := instFintype n
    exact inferInstanceAs (Fintype (Layout (n + 1) ⊕ Layout n))

instance instDecidableEq : (n : ℕ) → DecidableEq (Layout n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | 1 => inferInstanceAs (DecidableEq PUnit)
  | n + 2 => by
    letI := instDecidableEq (n + 1)
    letI := instDecidableEq n
    exact inferInstanceAs (DecidableEq (Layout (n + 1) ⊕ Layout n))

/-- The right endpoints of the dominoes. The pairs are `{i-1,i}`. -/
def dominoes : {n : ℕ} → Layout n → Finset ℕ
  | 0, _ => ∅
  | 1, _ => ∅
  | _n + 2, Sum.inl T => dominoes T
  | n + 2, Sum.inr T => insert (n + 1) (dominoes T)

/-- Exact admissibility of a domino-index set on a finite line. -/
def Legal (n : ℕ) (D : Finset ℕ) : Prop :=
  (∀ i ∈ D, 0 < i ∧ i < n) ∧ ∀ i ∈ D, i + 1 ∉ D

instance (n : ℕ) (D : Finset ℕ) : Decidable (Legal n D) :=
  inferInstanceAs (Decidable ((∀ i ∈ D, 0 < i ∧ i < n) ∧ ∀ i ∈ D, i + 1 ∉ D))

@[simp] theorem legal_empty (n : ℕ) : Legal n ∅ := by simp [Legal]

private theorem legal_mono {n m : ℕ} {D : Finset ℕ} (hD : Legal n D) (hnm : n ≤ m) :
    Legal m D := by
  exact ⟨fun i hi => ⟨(hD.1 i hi).1, lt_of_lt_of_le (hD.1 i hi).2 hnm⟩, hD.2⟩

private theorem legal_insert {n : ℕ} {D : Finset ℕ} (hD : Legal n D) :
    Legal (n + 2) (insert (n + 1) D) := by
  constructor
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · have := hD.1 i hi; omega
  · intro i hi hs
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rcases Finset.mem_insert.mp hs with hs | hs
      · omega
      · have := hD.1 _ hs; omega
    · rcases Finset.mem_insert.mp hs with hs | hs
      · have := hD.1 i hi; omega
      · exact hD.2 i hi hs

/-- The layout encoding always consists of disjoint, in-range dominoes. -/
theorem dominoes_legal : {n : ℕ} → (T : Layout n) → Legal n (dominoes T)
  | 0, _ => legal_empty _
  | 1, _ => legal_empty _
  | n + 2, Sum.inl T => legal_mono (dominoes_legal T) (by omega)
  | n + 2, Sum.inr T => legal_insert (dominoes_legal T)

private theorem top_not_mem {n : ℕ} (T : Layout n) : n ∉ dominoes T := by
  intro h
  have := (dominoes_legal T).1 n h
  omega

private theorem succ_top_not_mem {n : ℕ} (T : Layout n) : n + 1 ∉ dominoes T := by
  intro h
  have := (dominoes_legal T).1 (n + 1) h
  omega

/-- A legal line has only one encoding; the construction adds no tile order. -/
theorem dominoes_injective (n : ℕ) : Function.Injective (@dominoes n) := by
  induction n using Nat.twoStepInduction with
  | zero => intro a b _; exact Subsingleton.elim _ _
  | one => intro a b _; exact Subsingleton.elim _ _
  | more n ih₀ ih₁ =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (ih₁ h)
      | inr b =>
        have hm : n + 1 ∈ @dominoes (n + 2) (Sum.inr b) := by
          simp [dominoes]
        rw [← h] at hm
        exact (top_not_mem a hm).elim
    | inr a =>
      cases b with
      | inl b =>
        have hm : n + 1 ∈ @dominoes (n + 2) (Sum.inr a) := by
          simp [dominoes]
        rw [h] at hm
        exact (top_not_mem b hm).elim
      | inr b =>
        apply congrArg Sum.inr
        apply ih₀
        have he := congrArg (fun D : Finset ℕ => D.erase (n + 1)) h
        simpa [dominoes, succ_top_not_mem] using he

/-- Every disjoint domino set is represented by a layout. -/
theorem exists_layout (n : ℕ) (D : Finset ℕ) (hD : Legal n D) :
    ∃ T : Layout n, dominoes T = D := by
  induction n using Nat.twoStepInduction generalizing D with
  | zero =>
    have hd : D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := hD.1 i hi
      omega
    exact ⟨PUnit.unit, hd.symm⟩
  | one =>
    have hd : D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := hD.1 i hi
      omega
    exact ⟨PUnit.unit, hd.symm⟩
  | more n ih₀ ih₁ =>
    by_cases ht : n + 1 ∈ D
    · have he : Legal n (D.erase (n + 1)) := by
        constructor
        · intro i hi
          have him := (Finset.mem_erase.mp hi).2
          have hne := (Finset.mem_erase.mp hi).1
          have hib := hD.1 i him
          have hin : i ≠ n := by
            intro hh
            subst i
            exact hD.2 n him ht
          omega
        · intro i hi hsi
          exact hD.2 i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hsi)
      obtain ⟨T, hT⟩ := ih₀ (D.erase (n + 1)) he
      refine ⟨Sum.inr T, ?_⟩
      simpa [dominoes, hT] using Finset.insert_erase ht
    · have he : Legal (n + 1) D := by
        constructor
        · intro i hi
          have := hD.1 i hi
          have hin : i ≠ n + 1 := by intro hh; subst i; exact ht hi
          omega
        · exact hD.2
      obtain ⟨T, hT⟩ := ih₁ D he
      exact ⟨Sum.inl T, hT⟩

/-- The finite layout type is equivalent to the actual legal domino subsets. -/
noncomputable def equivLegal (n : ℕ) : Layout n ≃ {D : Finset ℕ // Legal n D} :=
  Equiv.ofBijective (fun T => ⟨dominoes T, dominoes_legal T⟩)
    ⟨fun _ _ h => dominoes_injective n (congrArg Subtype.val h), by
      intro D
      obtain ⟨T, hT⟩ := exists_layout n D.val D.property
      exact ⟨T, Subtype.ext hT⟩⟩

/-- The sites covered by singleton tiles. -/
def singletons : {n : ℕ} → Layout n → Finset ℕ
  | 0, _ => ∅
  | 1, _ => {0}
  | n + 2, Sum.inl T => insert (n + 1) (singletons T)
  | _n + 2, Sum.inr T => singletons T

/-- Every singleton index lies on the finite line. -/
theorem singletons_lt : {n : ℕ} → (T : Layout n) → ∀ i ∈ singletons T, i < n
  | 0, _, i, hi => by simp [singletons] at hi
  | 1, _, i, hi => by simp only [singletons, Finset.mem_singleton] at hi; omega
  | n + 2, Sum.inl T, i, hi => by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · have := singletons_lt T i hi; omega
  | n + 2, Sum.inr T, i, hi => by
    have := singletons_lt T i hi; omega

/-- Exact site partition: a site is single precisely when it lies on the
line and belongs to neither endpoint of any domino. -/
theorem mem_singletons_iff (n : ℕ) (T : Layout n) (i : ℕ) :
    i ∈ singletons T ↔ i < n ∧ i ∉ dominoes T ∧ i + 1 ∉ dominoes T := by
  induction n using Nat.twoStepInduction generalizing i with
  | zero => simp [singletons, dominoes]
  | one => simp [singletons, dominoes]
  | more n ih₀ ih₁ =>
    cases T with
    | inl T =>
      by_cases hi : i = n + 1
      · subst i
        have h₁ : n + 1 ∉ dominoes T := top_not_mem T
        have h₂ : n + 1 + 1 ∉ dominoes T := succ_top_not_mem T
        simp [singletons, dominoes, h₁, h₂]
      · simp only [singletons, dominoes, Finset.mem_insert, hi, false_or, ih₁]
        constructor
        · rintro ⟨h, h₁, h₂⟩
          exact ⟨by omega, h₁, h₂⟩
        · rintro ⟨h, h₁, h₂⟩
          exact ⟨by omega, h₁, h₂⟩
    | inr T =>
      simp only [singletons, dominoes, Finset.mem_insert, not_or, ih₀]
      constructor
      · rintro ⟨h, h₁, h₂⟩
        exact ⟨by omega, ⟨by omega, h₁⟩, ⟨by omega, h₂⟩⟩
      · rintro ⟨h, ⟨hne, h₁⟩, ⟨hne', h₂⟩⟩
        exact ⟨by omega, h₁, h₂⟩

/-- Each domino covers two sites and every other site is a singleton. -/
theorem card_singletons_add_twice_card_dominoes : {n : ℕ} → (T : Layout n) →
    (singletons T).card + 2 * (dominoes T).card = n
  | 0, _ => by simp [singletons, dominoes]
  | 1, _ => by simp [singletons, dominoes]
  | n + 2, Sum.inl T => by
    have hn : n + 1 ∉ singletons T := by
      intro h
      have := singletons_lt T _ h
      omega
    simp only [singletons, dominoes, Finset.card_insert_of_notMem hn]
    have := card_singletons_add_twice_card_dominoes T
    omega
  | n + 2, Sum.inr T => by
    simp only [singletons, dominoes, Finset.card_insert_of_notMem (succ_top_not_mem T)]
    have := card_singletons_add_twice_card_dominoes T
    omega

/-- The unpaired site count is determined by the domino set. -/
theorem card_singletons {n : ℕ} (T : Layout n) :
    (singletons T).card = n - 2 * (dominoes T).card := by
  have := card_singletons_add_twice_card_dominoes T
  omega

/-- Site zero is a singleton exactly when the first domino is absent. -/
theorem zero_mem_singletons_iff (n : ℕ) (hn : 0 < n) (T : Layout n) :
    0 ∈ singletons T ↔ 1 ∉ dominoes T := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => simp [singletons, dominoes]
  | more n ih₀ ih₁ =>
    cases T with
    | inl T =>
      simpa [singletons, dominoes] using ih₁ (by omega) T
    | inr T =>
      cases n with
      | zero => simp [singletons, dominoes]
      | succ n =>
        simpa [singletons, dominoes, show 1 ≠ n + 1 + 1 by omega] using ih₀ (by omega) T

section Weights

variable {R : Type*} [CommSemiring R]

/-- Product of the actual tile weights: the singleton at site `i` has weight
`a i`, and a domino with right endpoint `i` has weight `b i`. -/
def weight (a b : ℕ → R) : {n : ℕ} → Layout n → R
  | 0, _ => 1
  | 1, _ => a 0
  | n + 2, Sum.inl T => weight a b T * a (n + 1)
  | n + 2, Sum.inr T => weight a b T * b (n + 1)

/-- Sum over all layouts; each legal tiling occurs exactly once. -/
def total (a b : ℕ → R) (n : ℕ) : R := ∑ T : Layout n, weight a b T

@[simp] theorem total_zero (a b : ℕ → R) : total a b 0 = 1 := by
  change ∑ T : PUnit, (1 : R) = 1
  simp

@[simp] theorem total_one (a b : ℕ → R) : total a b 1 = a 0 := by
  change ∑ T : PUnit, a 0 = a 0
  simp

/-- Partition by the rightmost tile, with disjoint and exhaustive branches. -/
theorem total_recurrence (a b : ℕ → R) (n : ℕ) :
    total a b (n + 2) = total a b (n + 1) * a (n + 1) + total a b n * b (n + 1) := by
  change (∑ T : Layout (n + 1) ⊕ Layout n, _) = _
  rw [Fintype.sum_sum_type]
  simp only [weight, ← Finset.sum_mul]
  rfl

/-- The two-site enumeration has exactly the two expected physical layouts. -/
theorem total_two (a b : ℕ → R) :
    total a b 2 = a 0 * a 1 + b 1 := by
  rw [show (2 : ℕ) = 0 + 2 by rfl, total_recurrence]
  simp

/-- The three-site enumeration consists of three physical layouts. -/
theorem total_three (a b : ℕ → R) :
    total a b 3 = a 0 * a 1 * a 2 + b 1 * a 2 + a 0 * b 2 := by
  rw [show (3 : ℕ) = 1 + 2 by rfl, total_recurrence, total_two, total_one]
  ring

/-- Multiplication over the actual singleton and domino sets. -/
theorem weight_eq_products (a b : ℕ → R) : {n : ℕ} → (T : Layout n) →
    weight a b T = (∏ i ∈ singletons T, a i) * ∏ i ∈ dominoes T, b i
  | 0, _ => by simp [weight, singletons, dominoes]
  | 1, _ => by simp [weight, singletons, dominoes]
  | n + 2, Sum.inl T => by
    have hn : n + 1 ∉ singletons T := by
      intro h
      have := singletons_lt T _ h
      omega
    simp only [weight, singletons, dominoes, Finset.prod_insert hn, weight_eq_products a b T]
    ring
  | n + 2, Sum.inr T => by
    simp only [weight, singletons, dominoes, Finset.prod_insert (succ_top_not_mem T),
      weight_eq_products a b T]
    ring

/-- Only weights of sites and dominoes actually on the finite line matter. -/
theorem weight_congr {a b a' b' : ℕ → R} {n : ℕ}
    (ha : ∀ i, i < n → a i = a' i)
    (hb : ∀ i, 0 < i → i < n → b i = b' i) (T : Layout n) :
    weight a b T = weight a' b' T := by
  rw [weight_eq_products, weight_eq_products]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact ha i (singletons_lt T i hi)
  · apply Finset.prod_congr rfl
    intro i hi
    exact hb i ((dominoes_legal T).1 i hi).1 ((dominoes_legal T).1 i hi).2

/-- Equality of all physically relevant tile weights gives equality of sums. -/
theorem total_congr {a b a' b' : ℕ → R} {n : ℕ}
    (ha : ∀ i, i < n → a i = a' i)
    (hb : ∀ i, 0 < i → i < n → b i = b' i) :
    total a b n = total a' b' n := by
  exact Finset.sum_congr rfl (fun T _ => weight_congr ha hb T)

end Weights

noncomputable section

/-- Modified singleton weights: site zero has half the other singleton weight. -/
def modifiedSingleton (x : Polynomial ℂ) (i : ℕ) : Polynomial ℂ :=
  if i = 0 then x else 2 * x

/-- A product of modified singleton weights contains one factor of one half
exactly when the site zero occurs. -/
theorem prod_modifiedSingleton (x : Polynomial ℂ) (S : Finset ℕ) :
    (∏ i ∈ S, modifiedSingleton x i) =
      (if 0 ∈ S then C (1 / 2 : ℂ) else 1) * (2 * x) ^ S.card := by
  have hfactor (i : ℕ) : modifiedSingleton x i =
      (if i = 0 then C (1 / 2 : ℂ) else 1) * (2 * x) := by
    by_cases hi : i = 0
    · simp only [modifiedSingleton, hi, ↓reduceIte]
      have hc : C (1 / 2 : ℂ) * (2 : Polynomial ℂ) = 1 := by
        rw [← C_ofNat 2, ← C_mul]
        norm_num
      calc x = 1 * x := (one_mul x).symm
           _ = C (1 / 2 : ℂ) * (2 * x) := by rw [← mul_assoc, hc]
    · simp [modifiedSingleton, hi]
  simp only [hfactor, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_ite_eq', mul_pow]

/-- Exact half-factor relating the modified line weight to uniform singleton
weights. This is the form needed for cutting a circle at site zero. -/
theorem weight_modified_eq (x : Polynomial ℂ) (b : ℕ → Polynomial ℂ)
    {n : ℕ} (hn : 0 < n) (T : Layout n) :
    weight (modifiedSingleton x) b T =
      (if 1 ∈ dominoes T then 1 else C (1 / 2 : ℂ)) *
        ((2 * x) ^ (n - 2 * (dominoes T).card) * ∏ i ∈ dominoes T, b i) := by
  rw [weight_eq_products, prod_modifiedSingleton, card_singletons]
  have hz := zero_mem_singletons_iff n hn T
  by_cases h : 1 ∈ dominoes T
  · have hzero : 0 ∉ singletons T := by simpa [h] using hz
    simp [h, hzero]
  · have hzero : 0 ∈ singletons T := hz.mpr h
    simp [h, hzero, mul_assoc]

/-- The original numerator's complex domino coefficient, including its sign. -/
def phaseDomino (t : ℕ → ℝ) (i : ℕ) : Polynomial ℂ :=
  -C ((1 - Complex.I * (t i : ℂ)) * (1 + Complex.I * (t (i - 1) : ℂ)))

/-- The actual finite tiling sum is M14's denominator-cleared numerator. -/
theorem total_eq_numerator (t : ℕ → ℝ) (ht : t 0 = 0) (n : ℕ) :
    total (modifiedSingleton X) (phaseDomino t) n = numerator t n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [modifiedSingleton, ht]
  | more n ih₀ ih₁ =>
    rw [total_recurrence, ih₀, ih₁, numerator_recurrence]
    simp only [modifiedSingleton, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, phaseDomino, Nat.add_sub_cancel]
    ring

end
end QFixLean.QuasiChebyshev.LineTiling
