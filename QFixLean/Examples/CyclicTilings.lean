module

public import QFixLean.Polynomial.TilingWeights

/-!
# Exact cycle-tiling checks

The length-nine tiling has three dominoes and a stabilizer of order three.
It gives three distinct rotated tilings, each counted three times when all
nine rotation parameters are summed. This explicitly tests the multiplicity
that a full-orbit assumption would miss.
-/

@[expose] public section

namespace QFixLean.Examples.CyclicTilings

noncomputable section

open QFixLean.QuasiChebyshev
open scoped BigOperators

set_option maxRecDepth 4096

/-- Dominoes cover `{1,0}`, `{4,3}`, `{7,6}`. -/
def periodicNine : Finset (ZMod 9) := {1, 4, 7}

theorem periodicNine_legal : IsCyclicTiling periodicNine := by
  unfold IsCyclicTiling
  decide

theorem periodicNine_card : periodicNine.card = 3 := by decide

theorem periodicNine_covered : covered periodicNine = {0, 1, 3, 4, 6, 7} := by decide

theorem periodicNine_singles : singles periodicNine = {2, 5, 8} := by decide

/-- This actual legal tiling lies in the three-domino stratum. -/
def periodicNineTiling : CyclicTilingCard 9 3 :=
  ⟨periodicNine, periodicNine_legal, periodicNine_card⟩

/-- Three, rather than nine, distinct tilings occur under rotation. -/
theorem periodicNine_distinct_rotations :
    (Finset.univ.image (fun j : ZMod 9 => rotateTilings j periodicNine)).card = 3 := by
  decide

/-- Each of those three tilings occurs for exactly three parameters. -/
theorem periodicNine_rotation_multiplicity :
    ∀ E ∈ Finset.univ.image (fun j : ZMod 9 => rotateTilings j periodicNine),
      (Finset.univ.filter (fun j : ZMod 9 => rotateTilings j periodicNine = E)).card = 3 := by
  decide

/-- The complete rotation fiber consists of the shifts `0`, `3`, and `6`. -/
theorem periodicNine_stabilizer :
    Finset.univ.filter (fun j : ZMod 9 => rotateTilings j periodicNine = periodicNine) =
      {0, 3, 6} := by decide

/-- The general by-cardinality rotation equivalence applies also to this periodic tiling. -/
theorem periodicNine_rotations_legal (j : ZMod 9) :
    IsCyclicTiling ((rotateTilingCardEquiv j periodicNineTiling).val) ∧
      ((rotateTilingCardEquiv j periodicNineTiling).val).card = 3 :=
  (rotateTilingCardEquiv j periodicNineTiling).property

/-- A length-one cycle has no legal dominoes. -/
theorem length_one_no_domino (D : Finset (ZMod 1)) (hD : IsCyclicTiling D) : D = ∅ :=
  (isCyclicTiling_one_iff D).mp hD

/-- The weight theorem sums all nine parameters, even though the orbit
contains only three distinct tilings. -/
theorem periodicNine_polynomial_rotation_sum :
    (∑ j : ZMod 9, tilingFactorPolynomial (rotateTilings j periodicNine)) =
      Polynomial.C (9 : ℂ) * (1 - Polynomial.X ^ 2) ^ 3 := by
  simpa only [periodicNine_card, Nat.cast_ofNat] using
    tilingFactorPolynomial_rotation_sum (by decide : Odd 9) periodicNine periodicNine_legal

/-- The scalar version also retains the multiplicity of every rotation. -/
theorem periodicNine_weight_rotation_sum (y : ℂ) :
    (∑ j : ZMod 9, tilingFactor (rotateTilings j periodicNine) y) =
      (9 : ℂ) * (1 - y ^ 2) ^ 3 := by
  simpa only [periodicNine_card, Nat.cast_ofNat] using
    tilingFactor_rotation_sum (by decide : Odd 9) periodicNine periodicNine_legal y

/-- The periodic example is included in the domain of the general
three-domino comparison; the double sum has no full-orbit premise. -/
theorem periodicNine_card_stratum_nonempty : Nonempty (CyclicTilingCard 9 3) :=
  ⟨periodicNineTiling⟩

theorem nine_three_domino_total_comparison (y : ℂ) :
    (∑ D : CyclicTilingCard 9 3, tilingFactor D.1 y) =
      ∑ _D : CyclicTilingCard 9 3, (1 - y ^ 2) ^ 3 :=
  tilingFactor_total_eq (by decide : Odd 9) 3 y

end

end QFixLean.Examples.CyclicTilings
