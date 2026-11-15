module

public import QFixLean.Polynomial.CyclicTangentSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact cyclic tangent checks

The length-three computation expands all three translation parameters and
uses exact trigonometric values, independently of the general cyclic sum
theorem. Repeating an index gives a different answer, so the distinct-index
condition cannot be dropped.
-/

@[expose] public section

namespace QFixLean.Examples

noncomputable section

open QFixLean.QuasiChebyshev

/-- The length-one cycle has an empty product and a unique nonempty product. -/
theorem cyclic_one_boundary_direct :
    (∑ j : ZMod 1, ∏ m ∈ (∅ : Finset (ZMod 1)), cyclicZ 1 (m + j)) = 1 ∧
      (∑ j : ZMod 1, ∏ m ∈ (Finset.univ : Finset (ZMod 1)), cyclicZ 1 (m + j)) = 0 := by
  constructor
  · simp
  · apply Finset.sum_eq_zero
    intro j _
    apply Finset.prod_eq_zero (i := 0) (Finset.mem_univ _)
    rw [Subsingleton.elim ((0 : ZMod 1) + j) 0, cyclicZ_zero]

theorem cyclic_three_zero : cyclicZ 3 0 = 0 := cyclicZ_zero 3

theorem cyclic_three_one : cyclicZ 3 1 = Complex.I * (Real.sqrt 3 : ℂ) := by
  simp [cyclicZ, cyclicTangent, cyclicArgument, ZMod.val_one, Real.tan_pi_div_three]

theorem cyclic_three_two : cyclicZ 3 2 = -Complex.I * (Real.sqrt 3 : ℂ) := by
  have harg : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  change Complex.I * (Real.tan ((2 : ℝ) * Real.pi / 3) : ℂ) = _
  rw [harg, Real.tan_pi_sub, Real.tan_pi_div_three]
  simp

/-- Direct three-term calculation, without the general cyclic sum identity. -/
theorem cyclic_three_pair_direct :
    (∑ j : ZMod 3, cyclicZ 3 j * cyclicZ 3 (1 + j)) = 3 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [cyclic_three_zero, cyclic_three_one, cyclic_three_two,
    show (1 : ZMod 3) + 1 = 2 by decide,
    show (1 : ZMod 3) + 2 = 0 by decide,
    show (3 : ZMod 3) = 0 by decide]
  have hs : (Real.sqrt 3 : ℂ)^2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  simp only [Complex.I_sq, hs]
  norm_num
  exact cyclic_three_zero

/-- The direct computation in the same set-product notation as the general theorem. -/
theorem cyclic_three_set_direct :
    (∑ j : ZMod 3, ∏ m ∈ ({0, 1} : Finset (ZMod 3)), cyclicZ 3 (m + j)) = 3 := by
  simpa only [Finset.prod_insert (show (0 : ZMod 3) ∉ ({1} : Finset (ZMod 3)) by decide),
    Finset.prod_singleton, zero_add] using cyclic_three_pair_direct

/-- The same set-product identity, now obtained from the general theorem. -/
theorem cyclic_three_set_formula :
    (∑ j : ZMod 3, ∏ m ∈ ({0, 1} : Finset (ZMod 3)), cyclicZ 3 (m + j)) = 3 := by
  change cyclicTangentSum 3 {0, 1} = 3
  rw [cyclicTangentSum_eq (by decide)]
  have hc : ({0, 1} : Finset (ZMod 3)).card = 2 := by decide
  rw [hc]
  norm_num

/-- Both length-one boundary cases are covered by the general interface. -/
theorem cyclic_one_boundary_formula :
    cyclicTangentSum 1 ∅ = 1 ∧ cyclicTangentSum 1 Finset.univ = 0 := by
  constructor <;> rw [cyclicTangentSum_eq (by decide)] <;>
    norm_num [Finset.card_univ, ZMod.card]

theorem cyclic_three_odd_examples :
    cyclicTangentSum 3 {1} = 0 ∧ cyclicTangentSum 3 Finset.univ = 0 := by
  constructor <;> rw [cyclicTangentSum_eq (by decide)] <;>
    norm_num [Finset.card_univ, ZMod.card]
  decide

/-- Nonadjacent indices on a composite cycle require no primality hypothesis. -/
theorem cyclic_nine_pair : cyclicTangentSum 9 {0, 3} = 9 := by
  rw [cyclicTangentSum_eq (by decide)]
  have hc : ({0, 3} : Finset (ZMod 9)).card = 2 := by decide
  rw [hc]
  norm_num

/-- All nine shifts are retained even for a set with a shorter translation orbit. -/
theorem cyclic_nine_periodic_sum : cyclicTangentSum 9 {0, 3, 6} = 0 := by
  rw [cyclicTangentSum_eq (by decide)]
  have hc : ({0, 3, 6} : Finset (ZMod 9)).card = 3 := by decide
  rw [hc]
  norm_num
  decide

/-- Zero scaling preserves the empty product and annihilates a nonempty one. -/
theorem cyclic_gamma_one_examples :
    (∑ j : ZMod 3, ∏ m ∈ (∅ : Finset (ZMod 3)),
      Complex.I * (tangent 3 1 (m + j).val : ℂ)) = 3 ∧
      (∑ j : ZMod 3, ∏ m ∈ ({0, 1} : Finset (ZMod 3)),
        Complex.I * (tangent 3 1 (m + j).val : ℂ)) = 0 := by
  constructor
  · have h := cyclicTangentSum_phase_gamma_one (L := 3) (by decide) ∅
    rw [ite_eq_left rfl] at h
    exact h
  · have hne : ({0, 1} : Finset (ZMod 3)) ≠ ∅ := by decide
    simpa only [hne, ite_false] using
      cyclicTangentSum_phase_gamma_one (L := 3) (by decide) {0, 1}

/-- Repetition is not equivalent to a two-element set of distinct indices. -/
theorem cyclic_three_repeated_index :
    (∑ j : ZMod 3, cyclicZ 3 j ^ 2) = -6 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [cyclic_three_zero, cyclic_three_one, cyclic_three_two]
  have hs : (Real.sqrt 3 : ℂ)^2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  simp only [Complex.I_sq, hs]
  norm_num

/-- This set has three distinct translates, despite nine translation parameters. -/
theorem cyclic_nine_periodic_translate_count :
    (Finset.univ.image fun j : ZMod 9 =>
      ({0, 3, 6} : Finset (ZMod 9)).image (fun m => m + j)).card = 3 ∧
      Fintype.card (ZMod 9) = 9 := by
  decide

end
end QFixLean.Examples
