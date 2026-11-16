module

public import QFixLean.Polynomial.LineTilings
public import QFixLean.Polynomial.CircleTilings

/-!
# Cutting and gluing weighted line layouts

The finite layout type is bijective with the cyclic tilings without the
wraparound domino. The product formula, including the half weight at site
zero, identifies their actual sums.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open Polynomial
open scoped BigOperators

/-- Cutting and gluing is a bijection of physical layouts, with no multiplicity. -/
def layoutNoWrapEquiv (L : ℕ) [NeZero L] :
    LineTiling.Layout L ≃ {D : CyclicTiling L // 0 ∉ D.val} :=
  (LineTiling.equivLegal L).trans ((noWrapLineEquiv L).symm.trans
    (Equiv.subtypeSubtypeEquivSubtypeInter IsCyclicTiling (fun D => 0 ∉ D)).symm)

@[simp] theorem layoutNoWrapEquiv_val {L : ℕ} [NeZero L] (T : LineTiling.Layout L) :
    (layoutNoWrapEquiv L T).val.val = lineToCycle L (LineTiling.dominoes T) := rfl

/-- The cast is injective on the bounded domino indices. -/
theorem LineTiling.Legal.cast_injOn {L : ℕ} {D : Finset ℕ} (hD : LineTiling.Legal L D) :
    Set.InjOn (Nat.cast : ℕ → ZMod L) D := by
  intro m hm n hn h
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt (hD.1 m hm).2,
    ZMod.val_natCast_of_lt (hD.1 n hn).2] using hv

/-- The no-wrap map preserves the number of dominoes. -/
theorem LineTiling.Legal.lineToCycle_card {L : ℕ} {D : Finset ℕ}
    (hD : LineTiling.Legal L D) : (lineToCycle L D).card = D.card :=
  Finset.card_image_iff.mpr hD.cast_injOn

/-- A bounded line index belongs to the glued cycle precisely when it belonged
before gluing. -/
theorem LineTiling.Legal.mem_lineToCycle {L : ℕ} {D : Finset ℕ}
    (hD : LineTiling.Legal L D) (i : ℕ) (hi : i < L) :
    (i : ZMod L) ∈ lineToCycle L D ↔ i ∈ D := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hD.1 j hj).2, ZMod.val_natCast_of_lt hi] at hv
    simpa [hv] using hj
  · intro h
    exact Finset.mem_image.mpr ⟨i, h, rfl⟩

/-- Products on the physical line are preserved by the cut-and-glue map. -/
theorem LineTiling.Legal.prod_lineToCycle {L : ℕ} {D : Finset ℕ}
    (hD : LineTiling.Legal L D) (b : ZMod L → Polynomial ℂ) :
    (∏ i ∈ lineToCycle L D, b i) = ∏ i ∈ D, b (i : ZMod L) :=
  Finset.prod_image hD.cast_injOn

/-- Pointwise equality of the actual modified-line product and the cut weight. -/
theorem layout_weight_eq_cutWeight {L : ℕ} [NeZero L] (hL : 1 < L)
    (x : Polynomial ℂ) (b : ZMod L → Polynomial ℂ) (T : LineTiling.Layout L) :
    LineTiling.weight (LineTiling.modifiedSingleton x) (fun n => b (n : ZMod L)) T =
      cutWeight (fun D => cyclicWeight x b D.val) (layoutNoWrapEquiv L T).val := by
  rw [LineTiling.weight_modified_eq x _ (by omega)]
  have hD := LineTiling.dominoes_legal T
  have hz : (0 : ZMod L) ∉ lineToCycle L (LineTiling.dominoes T) :=
    IsLineDominoSet.zero_not_mem hD
  have h1 : (1 : ZMod L) ∈ lineToCycle L (LineTiling.dominoes T) ↔
      (1 : ℕ) ∈ LineTiling.dominoes T := by simpa using hD.mem_lineToCycle 1 hL
  simp only [cutWeight, layoutNoWrapEquiv_val, hz, ↓reduceIte,
    h1, cyclicWeight, hD.lineToCycle_card,
    hD.prod_lineToCycle]
  by_cases h : 1 ∈ LineTiling.dominoes T <;> simp [h]

/-- The total actual line sum is the sum over no-wrap cyclic tilings. -/
theorem total_eq_sum_noWrap {L : ℕ} [NeZero L] (hL : 1 < L)
    (x : Polynomial ℂ) (b : ZMod L → Polynomial ℂ) :
    LineTiling.total (LineTiling.modifiedSingleton x) (fun n => b (n : ZMod L)) L =
      ∑ D : {D : CyclicTiling L // 0 ∉ D.val},
        cutWeight (fun D => cyclicWeight x b D.val) D.val := by
  exact Fintype.sum_equiv (layoutNoWrapEquiv L) _ _
    (layout_weight_eq_cutWeight hL x b)

/-- Wraparound terms have zero cut weight, so extending to all cyclic tilings
adds no terms. -/
theorem sum_cutWeight_eq_sum_noWrap {L : ℕ} [NeZero L]
    (W : CyclicTiling L → Polynomial ℂ) :
    ∑ D : CyclicTiling L, cutWeight W D =
      ∑ D : {D : CyclicTiling L // 0 ∉ D.val}, cutWeight W D.val := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun D : CyclicTiling L => 0 ∉ D.val)
    (cutWeight W)
  have hz : (∑ D : {D : CyclicTiling L // ¬(0 ∉ D.val)}, cutWeight W D.val) = 0 := by
    apply Finset.sum_eq_zero
    intro D _
    simp [cutWeight, Classical.not_not.mp D.property]
  rw [hz, add_zero] at h
  exact h.symm

/-- Actual line enumeration agrees with the complete cyclic cut sum. -/
theorem total_eq_sum_cutWeight {L : ℕ} [NeZero L] (hL : 1 < L)
    (x : Polynomial ℂ) (b : ZMod L → Polynomial ℂ) :
    LineTiling.total (LineTiling.modifiedSingleton x) (fun n => b (n : ZMod L)) L =
      ∑ D : CyclicTiling L, cutWeight (fun D => cyclicWeight x b D.val) D := by
  rw [sum_cutWeight_eq_sum_noWrap]
  exact total_eq_sum_noWrap hL x b

/-- Reflection-invariant domino weights make the full circle sum exactly twice
its actual modified-line enumeration. -/
theorem sum_cyclic_eq_twice_line {L : ℕ} [NeZero L] (hL : 1 < L)
    (x : Polynomial ℂ) (b : ZMod L → Polynomial ℂ)
    (hb : ∀ n, b (1 - n) = b n) :
    (∑ D : CyclicTiling L, cyclicWeight x b D.val) =
      2 * LineTiling.total (LineTiling.modifiedSingleton x)
        (fun n => b (n : ZMod L)) L := by
  rw [total_eq_sum_cutWeight hL]
  exact sum_cyclicWeight_eq_twice_cut _ (fun D => cyclicWeight_reflect x b hb D.val)

end
end QFixLean.QuasiChebyshev
