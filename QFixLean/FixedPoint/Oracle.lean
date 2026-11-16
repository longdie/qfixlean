module

public import QFixLean.Basic.Ancilla
public import QFixLean.Basic.PhaseRotation

/-!
# Target-controlled bit-flip queries and exact clean-ancilla phase implementation

The query primitive is `O_P = [[1-P,P],[P,1-P]]`, unitary on the whole
Hilbert extension. Its mathematical definition specifies its oracle semantics;
it does not make evaluating an unknown target projection a free operation.
P14, arXiv:1409.3305v2, Figure 2: two bit-flip queries implement a target
phase with an exactly restored ancilla. Here the ancilla phase is
`diag(1,exp(iφ))`, so no extra global phase is suppressed.
-/

@[expose] public section

namespace QFixLean.FixedPoint.Oracle

open Ancilla
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Raw continuous linear semantics, defined even before the projection laws. -/
def bitFlipOp (P : E →L[ℂ] E) : Space E →L[ℂ] Space E :=
  block (1 - P) P P (1 - P)

@[simp] theorem bitFlipOp_fst (P : E →L[ℂ] E) (x : Space E) :
    (bitFlipOp P x).fst = (1 - P) x.fst + P x.snd := rfl
@[simp] theorem bitFlipOp_snd (P : E →L[ℂ] E) (x : Space E) :
    (bitFlipOp P x).snd = P x.fst + (1 - P) x.snd := rfl

@[simp] theorem bitFlipOp_zero : bitFlipOp (0 : E →L[ℂ] E) = 1 := by
  ext x <;> simp

/-- The all-target oracle swaps the ancilla components. -/
theorem bitFlipOp_one (x : Space E) : bitFlipOp (1 : E →L[ℂ] E) x = mk x.snd x.fst := by
  ext <;> simp

variable [CompleteSpace E]

theorem bitFlipOp_mul_self {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    bitFlipOp P * bitFlipOp P = 1 := by
  ext x
  all_goals simp only [mul_apply_eq_comp, bitFlipOp_fst, bitFlipOp_snd, map_add,
    projection_apply_self hP, projection_apply_self hP.one_sub,
    projection_complement_apply hP, complement_projection_apply hP,
    add_zero, zero_add, one_apply_eq_self]
  · simpa only [add_comm] using projection_add_complement P x.fst
  · exact projection_add_complement P x.snd

theorem star_bitFlipOp {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    star (bitFlipOp P) = bitFlipOp P := by
  simp only [bitFlipOp, star_block, star_sub, star_one, hP.isSelfAdjoint.star_eq]

/-- The target-controlled bit-flip, bundled as a native unitary. -/
def bitFlip {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    unitary (Space E →L[ℂ] Space E) :=
  ⟨bitFlipOp P, by
    rw [Unitary.mem_iff, star_bitFlipOp hP, bitFlipOp_mul_self hP]
    exact ⟨rfl, rfl⟩⟩

@[simp] theorem coe_bitFlip {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    (bitFlip hP : Space E →L[ℂ] Space E) = bitFlipOp P := rfl

/-- A target component flips ancilla zero to one. -/
theorem bitFlip_target_zero {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    (bitFlip hP : Space E →L[ℂ] Space E) (mk (P v) 0) = mk 0 (P v) := by
  ext <;> simp only [coe_bitFlip, bitFlipOp_fst, bitFlipOp_snd, mk_fst, mk_snd,
    complement_projection_apply hP, projection_apply_self hP, map_zero, add_zero]

/-- A target component flips ancilla one to zero. -/
theorem bitFlip_target_one {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    (bitFlip hP : Space E →L[ℂ] Space E) (mk 0 (P v)) = mk (P v) 0 := by
  ext <;> simp only [coe_bitFlip, bitFlipOp_fst, bitFlipOp_snd, mk_fst, mk_snd,
    complement_projection_apply hP, projection_apply_self hP, map_zero, add_zero, zero_add]

theorem bitFlip_complement_zero {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    (bitFlip hP : Space E →L[ℂ] Space E) (mk ((1 - P) v) 0) = mk ((1 - P) v) 0 := by
  ext <;> simp only [coe_bitFlip, bitFlipOp_fst, bitFlipOp_snd, mk_fst, mk_snd,
    projection_complement_apply hP, projection_apply_self hP.one_sub,
    map_zero, add_zero]

theorem bitFlip_complement_one {P : E →L[ℂ] E} (hP : IsStarProjection P) (v : E) :
    (bitFlip hP : Space E →L[ℂ] Space E) (mk 0 ((1 - P) v)) = mk 0 ((1 - P) v) := by
  ext <;> simp only [coe_bitFlip, bitFlipOp_fst, bitFlipOp_snd, mk_fst, mk_snd,
    projection_complement_apply hP, projection_apply_self hP.one_sub,
    map_zero, add_zero, zero_add]

/-- An ancilla-only phase with its exact diagonal convention. -/
def ancillaPhaseOp (φ : ℝ) : Space E →L[ℂ] Space E :=
  block 1 0 0 (phaseFactor φ • 1)

omit [CompleteSpace E] in
@[simp] theorem ancillaPhaseOp_fst (φ : ℝ) (x : Space E) :
    (ancillaPhaseOp φ x).fst = x.fst := by simp [ancillaPhaseOp]
omit [CompleteSpace E] in
@[simp] theorem ancillaPhaseOp_snd (φ : ℝ) (x : Space E) :
    (ancillaPhaseOp φ x).snd = phaseFactor φ • x.snd := by simp [ancillaPhaseOp]

theorem ancillaPhaseOp_mem_unitary (φ : ℝ) :
    ancillaPhaseOp (E := E) φ ∈ unitary (Space E →L[ℂ] Space E) := by
  have hl : (starRingEnd ℂ) (phaseFactor φ) * phaseFactor φ = 1 :=
    phaseFactor_star_mul_self φ
  have hr : phaseFactor φ * (starRingEnd ℂ) (phaseFactor φ) = 1 := by
    rw [mul_comm, hl]
  rw [Unitary.mem_iff]
  constructor <;> ext x <;>
    simp [ancillaPhaseOp, star_block, smul_smul, hl, hr]

/-- Native unitary for the nonquery ancilla phase. -/
def ancillaPhase (φ : ℝ) : unitary (Space E →L[ℂ] Space E) :=
  ⟨ancillaPhaseOp φ, ancillaPhaseOp_mem_unitary φ⟩

@[simp] theorem coe_ancillaPhase (φ : ℝ) :
    (ancillaPhase (E := E) φ : Space E →L[ℂ] Space E) = ancillaPhaseOp φ := rfl

/-- Exactly two queries realize the selective data phase and restore ancilla zero,
for every data vector, with no input normalization or nondegeneracy premise. -/
theorem targetPhase_embed {P : E →L[ℂ] E} (hP : IsStarProjection P) (φ : ℝ) (v : E) :
    ((bitFlip hP * ancillaPhase φ * bitFlip hP : unitary (Space E →L[ℂ] Space E)) :
      Space E →L[ℂ] Space E) (embed v) = embed (phaseRotation P φ v) := by
  change bitFlipOp P (ancillaPhaseOp φ (bitFlipOp P (embed v))) = _
  ext
  all_goals simp only [bitFlipOp_fst, bitFlipOp_snd, ancillaPhaseOp_fst,
    ancillaPhaseOp_snd, embed_fst, embed_snd, map_zero, add_zero, map_smul,
    projection_apply_self hP, projection_apply_self hP.one_sub,
    projection_complement_apply hP, complement_projection_apply hP, smul_zero]
  exact (phaseRotation_apply_components P φ v).symm

/-- The restored ancilla can be reused immediately for another target phase. -/
theorem two_targetPhases_embed {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (φ θ : ℝ) (v : E) :
    ((bitFlip hP * ancillaPhase θ * bitFlip hP : unitary (Space E →L[ℂ] Space E)) :
      Space E →L[ℂ] Space E)
      (((bitFlip hP * ancillaPhase φ * bitFlip hP : unitary (Space E →L[ℂ] Space E)) :
        Space E →L[ℂ] Space E) (embed v)) =
      embed (phaseRotation P θ (phaseRotation P φ v)) := by
  rw [targetPhase_embed, targetPhase_embed]

end
end QFixLean.FixedPoint.Oracle
