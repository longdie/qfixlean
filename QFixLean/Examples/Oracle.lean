module

public import QFixLean.FixedPoint.Oracle
public import QFixLean.Examples.Measurement

/-!
# Exact bit-flip oracle and clean-ancilla checks

The first data basis state is marked. Computational basis checks include every
data/ancilla bit, while the two-component calculations retain amplitudes and
phases on superpositions. No floating-point calculations are used.
-/

@[expose] public section

namespace QFixLean.Examples

open Ancilla FixedPoint.Oracle
noncomputable section

/-- A two-bit computational basis state, with data bit first. -/
def oracleBasis (x b : Bool) : Space QubitSpace :=
  let v : QubitSpace := if x then (basisOne : QubitSpace) else (basisZero : QubitSpace)
  if b then mk 0 v else mk v 0

/-- Marking data zero implements exactly `b xor !x`, for all four basis inputs. -/
theorem firstBasisOracle_xor (x b : Bool) :
    (bitFlip firstBasisTarget_isStarProjection : Space QubitSpace →L[ℂ] Space QubitSpace)
      (oracleBasis x b) = oracleBasis x (Bool.xor b (!x)) := by
  cases x <;> cases b <;> apply Ancilla.ext <;>
    simp [oracleBasis, sub_apply]

/-- Full four-amplitude action, including arbitrary dirty ancilla input. -/
theorem firstBasisOracle_components (v : Space QubitSpace) :
    bitFlipOp firstBasisTarget v =
      mk (WithLp.toLp 2 ![v.snd 0, v.fst 1])
        (WithLp.toLp 2 ![v.fst 0, v.snd 1]) := by
  apply Ancilla.ext <;> ext i <;> fin_cases i <;>
    simp [bitFlipOp_fst, bitFlipOp_snd, firstBasisTarget_apply, sub_apply]

/-- The marked/unmarked rational superposition with an arbitrary ancilla vector. -/
theorem rationalState_oracle_superposition (a b : ℂ) :
    bitFlipOp firstBasisTarget
      (mk (a • (rationalState : QubitSpace)) (b • (rationalState : QubitSpace))) =
      mk (WithLp.toLp 2 ![b * (3 / 5), a * (4 / 5)])
        (WithLp.toLp 2 ![a * (3 / 5), b * (4 / 5)]) := by
  rw [firstBasisOracle_components]
  apply Ancilla.ext <;> ext i <;> fin_cases i <;> simp [rationalState]

/-- Direct first-query calculation before the ancilla phase. -/
theorem rationalState_oracle_first_query :
    bitFlipOp firstBasisTarget (embed (rationalState : QubitSpace)) =
      mk (WithLp.toLp 2 ![0, (4 / 5 : ℂ)])
        (WithLp.toLp 2 ![(3 / 5 : ℂ), 0]) := by
  rw [firstBasisOracle_components]
  apply Ancilla.ext <;> ext i <;> fin_cases i <;> simp [rationalState]

/-- Independent two-component calculation of `O Dφ O`, with exact ancilla reset.
This proof does not call the general target-phase or compilation theorem. -/
theorem rationalState_oracle_phase_direct (φ : ℝ) :
    bitFlipOp firstBasisTarget
      (ancillaPhaseOp φ (bitFlipOp firstBasisTarget (embed (rationalState : QubitSpace)))) =
      embed (WithLp.toLp 2 ![phaseFactor φ * (3 / 5 : ℂ), (4 / 5 : ℂ)]) := by
  rw [rationalState_oracle_first_query, firstBasisOracle_components]
  apply Ancilla.ext <;> ext i <;> fin_cases i <;> simp

/-- Native-unitary formulation of the same independently checked implementation. -/
theorem rationalState_oracle_phase_native (φ : ℝ) :
    ((bitFlip firstBasisTarget_isStarProjection * ancillaPhase φ *
        bitFlip firstBasisTarget_isStarProjection :
      unitary (Space QubitSpace →L[ℂ] Space QubitSpace)) :
        Space QubitSpace →L[ℂ] Space QubitSpace) (embed (rationalState : QubitSpace)) =
      embed (WithLp.toLp 2 ![phaseFactor φ * (3 / 5 : ℂ), (4 / 5 : ℂ)]) :=
  rationalState_oracle_phase_direct φ

/-- A second target phase immediately reuses the restored ancilla. -/
theorem rationalState_oracle_two_phases (φ θ : ℝ) :
    bitFlipOp firstBasisTarget (ancillaPhaseOp θ (bitFlipOp firstBasisTarget
      (bitFlipOp firstBasisTarget (ancillaPhaseOp φ (bitFlipOp firstBasisTarget
        (embed (rationalState : QubitSpace))))))) =
      embed (WithLp.toLp 2 ![phaseFactor θ * phaseFactor φ * (3 / 5 : ℂ), (4 / 5 : ℂ)]) := by
  rw [rationalState_oracle_phase_direct, firstBasisOracle_components,
    firstBasisOracle_components]
  apply Ancilla.ext <;> ext i <;> fin_cases i <;> simp [mul_assoc]

/-- Both target directions of a rank-two target acquire the same phase. -/
theorem threeLevel_oracle_phase_direct (φ : ℝ) :
    bitFlipOp firstTwoTarget (ancillaPhaseOp φ (bitFlipOp firstTwoTarget
      (embed (threeLevelState : ThreeLevelSpace)))) =
      embed (WithLp.toLp 2 ![phaseFactor φ * (1 / 3 : ℂ),
        phaseFactor φ * (2 / 3 : ℂ), (2 / 3 : ℂ)]) := by
  apply Ancilla.ext <;> ext i <;> fin_cases i <;>
    simp [bitFlipOp_fst, bitFlipOp_snd, ancillaPhaseOp_fst, ancillaPhaseOp_snd,
      sub_apply, firstTwoTarget_apply, threeLevelState]

/-- The completely successful data input flips the ancilla and remains valid. -/
theorem basisZero_oracle_clean :
    bitFlipOp firstBasisTarget (embed (basisZero : QubitSpace)) =
      mk 0 (basisZero : QubitSpace) := by
  apply Ancilla.ext <;> simp [sub_apply]

/-- The zero-success input has valid oracle semantics without a positive promise. -/
theorem basisOne_oracle_clean :
    bitFlipOp firstBasisTarget (embed (basisOne : QubitSpace)) =
      embed (basisOne : QubitSpace) := by
  apply Ancilla.ext <;> simp [sub_apply]

/-- The empty target never flips either input component. -/
theorem zeroTarget_oracle (v : Space QubitSpace) :
    bitFlipOp (0 : QubitSpace →L[ℂ] QubitSpace) v = v := by
  rw [bitFlipOp_zero]
  rfl

/-- The full target swaps the ancilla components for every input. -/
theorem fullTarget_oracle (v : Space QubitSpace) :
    bitFlipOp (1 : QubitSpace →L[ℂ] QubitSpace) v = mk v.snd v.fst :=
  bitFlipOp_one v

end
end QFixLean.Examples
