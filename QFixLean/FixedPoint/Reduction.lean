module

public import QFixLean.FixedPoint.PhaseSequence
public import QFixLean.FixedPoint.TwoDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Canonical bad/good coordinates for a fixed initial state

The normalized basis is used only under `0 < successWeight P ψ₀ < 1`.
Coordinates have bad direction first and good direction second, and use the
Euclidean norm. The ambient target may have arbitrary rank.
-/

@[expose] public section

namespace QFixLean.FixedPoint.Reduction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Coordinate := EuclideanSpace ℂ (Fin 2)

/-- Initial failure amplitude magnitude, with success probability as its input. -/
def failureAmplitude (ψ₀ : PureState E) (P : E →L[ℂ] E) : ℝ :=
  Real.sqrt (1 - successWeight P (ψ₀ : E))

/-- Initial success amplitude magnitude. -/
def successAmplitude (ψ₀ : PureState E) (P : E →L[ℂ] E) : ℝ :=
  Real.sqrt (successWeight P (ψ₀ : E))

/-- Normalized bad direction; normalization theorems require nonzero failure. -/
def badDirection (ψ₀ : PureState E) (P : E →L[ℂ] E) : E :=
  ((failureAmplitude ψ₀ P : ℂ)⁻¹) • ((1 - P) (ψ₀ : E))

/-- Normalized good direction; normalization theorems require nonzero success. -/
def goodDirection (ψ₀ : PureState E) (P : E →L[ℂ] E) : E :=
  ((successAmplitude ψ₀ P : ℂ)⁻¹) • (P (ψ₀ : E))

variable (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)

include hP in
theorem failureAmplitude_eq_norm : failureAmplitude ψ₀ P = ‖(1 - P) (ψ₀ : E)‖ := by
  have h := ψ₀.successWeight_add_failureWeight hP
  rw [failureAmplitude, show 1 - successWeight P (ψ₀ : E) =
    failureWeight P (ψ₀ : E) by linarith, failureWeight, Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace E] in
theorem successAmplitude_eq_norm : successAmplitude ψ₀ P = ‖P (ψ₀ : E)‖ := by
  rw [successAmplitude, successWeight, Real.sqrt_sq (norm_nonneg _)]

include hP in
theorem amplitude_sq_add : (failureAmplitude ψ₀ P) ^ 2 +
    (successAmplitude ψ₀ P) ^ 2 = 1 := by
  rw [failureAmplitude_eq_norm ψ₀ hP, successAmplitude_eq_norm]
  have h := ψ₀.successWeight_add_failureWeight hP
  unfold successWeight failureWeight at h
  linarith

include hP in
theorem successAmplitude_eq_sqrt_failure : successAmplitude ψ₀ P =
    Real.sqrt (1 - (failureAmplitude ψ₀ P) ^ 2) := by
  have h := amplitude_sq_add ψ₀ hP
  rw [show 1 - (failureAmplitude ψ₀ P) ^ 2 = (successAmplitude ψ₀ P) ^ 2 by linarith,
    Real.sqrt_sq (show 0 ≤ successAmplitude ψ₀ P from Real.sqrt_nonneg _)]

omit [CompleteSpace E] in
theorem failureAmplitude_pos (h1 : successWeight P (ψ₀ : E) < 1) :
    0 < failureAmplitude ψ₀ P := Real.sqrt_pos.mpr (sub_pos.mpr h1)

omit [CompleteSpace E] in
theorem successAmplitude_pos (h0 : 0 < successWeight P (ψ₀ : E)) :
    0 < successAmplitude ψ₀ P := Real.sqrt_pos.mpr h0

include hP in
theorem norm_badDirection (h1 : successWeight P (ψ₀ : E) < 1) :
    ‖badDirection ψ₀ P‖ = 1 := by
  have hp := failureAmplitude_pos ψ₀ h1
  rw [badDirection, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp, ← failureAmplitude_eq_norm ψ₀ hP, inv_mul_cancel₀ hp.ne']

omit [CompleteSpace E] in
theorem norm_goodDirection (h0 : 0 < successWeight P (ψ₀ : E)) :
    ‖goodDirection ψ₀ P‖ = 1 := by
  have hp := successAmplitude_pos ψ₀ h0
  rw [goodDirection, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp, ← successAmplitude_eq_norm ψ₀, inv_mul_cancel₀ hp.ne']

include hP in
theorem directions_inner : inner ℂ (badDirection ψ₀ P) (goodDirection ψ₀ P) = 0 := by
  have ho : inner ℂ ((1 - P) (ψ₀ : E)) (P (ψ₀ : E)) = 0 := by
    simpa only [sub_sub_cancel] using projection_inner_complement hP.one_sub (ψ₀ : E)
  simp only [badDirection, goodDirection, inner_smul_left, inner_smul_right, ho,
    mul_zero]

include hP in
theorem projection_badDirection : P (badDirection ψ₀ P) = 0 := by
  rw [badDirection, map_smul, projection_complement_apply hP, smul_zero]

include hP in
theorem projection_goodDirection : P (goodDirection ψ₀ P) = goodDirection ψ₀ P := by
  simp only [goodDirection, map_smul, projection_apply_self hP]

omit [CompleteSpace E] in
theorem source_decomposition (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) :
    (failureAmplitude ψ₀ P : ℂ) • badDirection ψ₀ P +
      (successAmplitude ψ₀ P : ℂ) • goodDirection ψ₀ P = (ψ₀ : E) := by
  have hx : (failureAmplitude ψ₀ P : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (failureAmplitude_pos ψ₀ h1).ne'
  have hy : (successAmplitude ψ₀ P : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (successAmplitude_pos ψ₀ h0).ne'
  simp only [badDirection, goodDirection, smul_smul, mul_inv_cancel₀ hx,
    mul_inv_cancel₀ hy, one_smul]
  simpa only [add_comm] using projection_add_complement P (ψ₀ : E)

/-- Linear synthesis of bad/good coordinates. It is an isometry on the
nondegenerate domain, as proved below; no claim is made outside that domain. -/
def embed (ψ₀ : PureState E) (P : E →L[ℂ] E) : Coordinate →ₗ[ℂ] E where
  toFun v := v 0 • badDirection ψ₀ P + v 1 • goodDirection ψ₀ P
  map_add' v w := by simp only [PiLp.add_apply, add_smul]; module
  map_smul' c v := by simp [smul_add, smul_smul]

omit [CompleteSpace E] in
theorem embed_apply (v : Coordinate) : embed ψ₀ P v =
    v 0 • badDirection ψ₀ P + v 1 • goodDirection ψ₀ P := rfl

include hP in
theorem embed_inner (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (v w : Coordinate) :
    inner ℂ (embed ψ₀ P v) (embed ψ₀ P w) = inner ℂ v w := by
  have hr : inner ℂ (badDirection ψ₀ P) (badDirection ψ₀ P) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_badDirection ψ₀ hP h1)
  have ht : inner ℂ (goodDirection ψ₀ P) (goodDirection ψ₀ P) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_goodDirection ψ₀ h0)
  have hrt := directions_inner ψ₀ hP
  have htr : inner ℂ (goodDirection ψ₀ P) (badDirection ψ₀ P) = 0 := by
    rw [← inner_conj_symm, hrt, map_zero]
  simp only [embed_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hr, ht, hrt, htr, mul_one, mul_zero, add_zero, zero_add]
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]

/-- The actual synthesis map as a native linear isometry. -/
def embedding (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) : Coordinate →ₗᵢ[ℂ] E :=
  (embed ψ₀ P).isometryOfInner (embed_inner ψ₀ hP h0 h1)

theorem embedding_apply (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (v : Coordinate) :
    embedding ψ₀ hP h0 h1 v = embed ψ₀ P v := rfl

omit [CompleteSpace E] in
theorem embed_initial (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) :
    embed ψ₀ P (TwoDimensional.initial (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P)) =
      (ψ₀ : E) := source_decomposition ψ₀ h0 h1

omit [CompleteSpace E] in
theorem range_embed (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) :
    LinearMap.range (embed ψ₀ P) = searchSpace ψ₀ P := by
  apply le_antisymm
  · rintro v ⟨c, rfl⟩
    exact (searchSpace ψ₀ P).add_mem
      ((searchSpace ψ₀ P).smul_mem _
        ((searchSpace ψ₀ P).smul_mem _ (bad_mem_searchSpace ψ₀ P)))
      ((searchSpace ψ₀ P).smul_mem _
        ((searchSpace ψ₀ P).smul_mem _ (good_mem_searchSpace ψ₀ P)))
  · intro v hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have hx : (failureAmplitude ψ₀ P : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (failureAmplitude_pos ψ₀ h1).ne'
    have hy : (successAmplitude ψ₀ P : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (successAmplitude_pos ψ₀ h0).ne'
    refine ⟨WithLp.toLp 2 ![a * (failureAmplitude ψ₀ P : ℂ),
      b * (successAmplitude ψ₀ P : ℂ)], ?_⟩
    simp [embed_apply, badDirection, goodDirection, smul_smul, mul_assoc,
      mul_inv_cancel₀ hx, mul_inv_cancel₀ hy]

include hP in
theorem embedding_injective (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) : Function.Injective (embed ψ₀ P) :=
  (embedding ψ₀ hP h0 h1).injective

include hP in
theorem projection_embed_components (v : Coordinate) :
    P (embed ψ₀ P v) = v 1 • goodDirection ψ₀ P := by
  simp only [embed_apply, map_add, map_smul, projection_badDirection ψ₀ hP,
    projection_goodDirection ψ₀ hP, smul_zero, zero_add]

include hP in
theorem complement_embed_components (v : Coordinate) :
    (1 - P) (embed ψ₀ P v) = v 0 • badDirection ψ₀ P := by
  rw [sub_apply, one_apply_eq_self, projection_embed_components ψ₀ hP, embed_apply,
    add_sub_cancel_right]

include hP in
theorem projection_embed (v : Coordinate) :
    P (embed ψ₀ P v) =
      embed ψ₀ P (TwoDimensional.applyMatrix TwoDimensional.targetProjection v) := by
  rw [projection_embed_components ψ₀ hP, embed_apply]
  simp [TwoDimensional.applyMatrix_apply, TwoDimensional.targetProjection]

include hP in
theorem sourceProjection_embed (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (v : Coordinate) :
    ψ₀.projection (embed ψ₀ P v) = embed ψ₀ P
      (TwoDimensional.applyMatrix
        (TwoDimensional.sourceProjection (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P)) v) := by
  have hi : inner ℂ (ψ₀ : E) (embed ψ₀ P v) =
      (failureAmplitude ψ₀ P : ℂ) * v 0 + (successAmplitude ψ₀ P : ℂ) * v 1 := by
    calc
      _ = inner ℂ (embed ψ₀ P
          (TwoDimensional.initial (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P)))
          (embed ψ₀ P v) := by rw [embed_initial ψ₀ h0 h1]
      _ = _ := by
        rw [embed_inner ψ₀ hP h0 h1]
        simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]
  rw [PureState.projection_apply, hi, ← source_decomposition ψ₀ h0 h1, embed_apply]
  simp only [TwoDimensional.applyMatrix_apply, TwoDimensional.sourceProjection,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  module

include hP in
theorem targetPhase_embed (α : ℝ) (v : Coordinate) :
    phaseRotation P α (embed ψ₀ P v) =
      embed ψ₀ P (TwoDimensional.applyMatrix (TwoDimensional.targetMatrix α) v) := by
  rw [phaseRotation, selectivePhase_apply, projection_embed_components ψ₀ hP]
  simp only [embed_apply, TwoDimensional.applyMatrix_apply, TwoDimensional.targetMatrix,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul, zero_mul, add_zero, zero_add]
  module

include hP in
theorem sourcePhase_embed (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (β : ℝ) (v : Coordinate) :
    phaseRotation ψ₀.projection β (embed ψ₀ P v) = embed ψ₀ P
      (TwoDimensional.applyMatrix
        (TwoDimensional.sourceMatrix (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P) β) v) := by
  rw [phaseRotation, selectivePhase_apply, sourceProjection_embed ψ₀ hP h0 h1,
    TwoDimensional.sourceMatrix, TwoDimensional.applyMatrix_add,
    TwoDimensional.applyMatrix_smul, TwoDimensional.applyMatrix_one, map_add, map_smul]

include hP in
/-- Exact intertwining on every coordinate vector, including its global phase. -/
theorem iterate_embed (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (α β : ℝ) (v : Coordinate) :
    (iterate ψ₀ hP α β : E →L[ℂ] E) (embed ψ₀ P v) = embed ψ₀ P
      (TwoDimensional.applyMatrix
        (TwoDimensional.iterateMatrix (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P) α β) v) := by
  rw [coe_iterate, mul_apply_eq_comp, targetPhase_embed ψ₀ hP,
    sourcePhase_embed ψ₀ hP h0 h1, TwoDimensional.iterateMatrix,
    TwoDimensional.applyMatrix_mul]

include hP in
/-- The same time-ordered list drives the actual and matrix products. -/
theorem execute_embed (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) (v : Coordinate) :
    (execute ψ₀ hP ps : E →L[ℂ] E) (embed ψ₀ P v) = embed ψ₀ P
      (TwoDimensional.applyMatrix
        (TwoDimensional.sequenceMatrix (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P) ps) v) := by
  induction ps generalizing v with
  | nil => simp
  | cons p ps ih =>
    change (execute ψ₀ hP ps : E →L[ℂ] E)
      ((iterate ψ₀ hP p.1 p.2 : E →L[ℂ] E) (embed ψ₀ P v)) = _
    rw [iterate_embed ψ₀ hP h0 h1, ih, TwoDimensional.sequenceMatrix_cons,
      TwoDimensional.applyMatrix_mul]

/-- Coordinates of the actual sequence output, rather than a probability model. -/
def outputCoordinates (ψ₀ : PureState E) (P : E →L[ℂ] E)
    (ps : List (ℝ × ℝ)) : Coordinate :=
  TwoDimensional.applyMatrix
    (TwoDimensional.sequenceMatrix (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P) ps)
    (TwoDimensional.initial (failureAmplitude ψ₀ P) (successAmplitude ψ₀ P))

include hP in
theorem output_eq_embed (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    (output ψ₀ hP ps : E) = embed ψ₀ P (outputCoordinates ψ₀ P ps) := by
  rw [coe_output, ← embed_initial ψ₀ h0 h1, execute_embed ψ₀ hP h0 h1]
  rfl

include hP in
theorem successWeight_embed (h0 : 0 < successWeight P (ψ₀ : E)) (v : Coordinate) :
    successWeight P (embed ψ₀ P v) = ‖v 1‖ ^ 2 := by
  rw [successWeight, projection_embed_components ψ₀ hP, norm_smul,
    norm_goodDirection ψ₀ h0, mul_one]

include hP in
theorem failureWeight_embed (h1 : successWeight P (ψ₀ : E) < 1) (v : Coordinate) :
    failureWeight P (embed ψ₀ P v) = ‖v 0‖ ^ 2 := by
  rw [failureWeight, complement_embed_components ψ₀ hP, norm_smul,
    norm_badDirection ψ₀ hP h1, mul_one]

include hP in
theorem output_successWeight (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    successWeight P (output ψ₀ hP ps : E) = ‖outputCoordinates ψ₀ P ps 1‖ ^ 2 := by
  rw [output_eq_embed ψ₀ hP h0 h1, successWeight_embed ψ₀ hP h0]

include hP in
theorem output_failureWeight (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    failureWeight P (output ψ₀ hP ps : E) = ‖outputCoordinates ψ₀ P ps 0‖ ^ 2 := by
  rw [output_eq_embed ψ₀ hP h0 h1, failureWeight_embed ψ₀ hP h1]

include hP in
theorem output_coordinate_weights_add (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) (ps : List (ℝ × ℝ)) :
    ‖outputCoordinates ψ₀ P ps 0‖ ^ 2 + ‖outputCoordinates ψ₀ P ps 1‖ ^ 2 = 1 := by
  rw [← output_failureWeight ψ₀ hP h0 h1, ← output_successWeight ψ₀ hP h0 h1]
  have h := (output ψ₀ hP ps).successWeight_add_failureWeight hP
  linarith

include hP in
/-- The rank-one target direction agrees with P on K, not on all of E. -/
theorem target_rankOne_on_searchSpace (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) {v : E} (hv : v ∈ searchSpace ψ₀ P) :
    InnerProductSpace.rankOne ℂ (goodDirection ψ₀ P) (goodDirection ψ₀ P) v = P v := by
  rw [← range_embed ψ₀ h0 h1] at hv
  obtain ⟨c, rfl⟩ := hv
  have ht : inner ℂ (goodDirection ψ₀ P) (goodDirection ψ₀ P) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_goodDirection ψ₀ h0)
  have htr : inner ℂ (goodDirection ψ₀ P) (badDirection ψ₀ P) = 0 := by
    rw [← inner_conj_symm, directions_inner ψ₀ hP, map_zero]
  rw [InnerProductSpace.rankOne_apply, projection_embed_components ψ₀ hP]
  simp only [embed_apply, inner_add_right, inner_smul_right, htr, ht, mul_zero,
    mul_one, zero_add]

/-- The native isometry has exactly the original component span as its range. -/
theorem embedding_range (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) :
    LinearMap.range (embedding ψ₀ hP h0 h1).toLinearMap = searchSpace ψ₀ P :=
  range_embed ψ₀ h0 h1

include hP in
/-- P14's rank-one target-direction phase equals the general target phase on K.
No equality on the rest of the ambient Hilbert space is asserted. -/
theorem targetPhase_rankOne_on_searchSpace (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) {v : E} (hv : v ∈ searchSpace ψ₀ P)
    (α : ℝ) :
    phaseRotation (InnerProductSpace.rankOne ℂ (goodDirection ψ₀ P)
      (goodDirection ψ₀ P)) α v = phaseRotation P α v := by
  simp only [phaseRotation, selectivePhase_apply,
    target_rankOne_on_searchSpace ψ₀ hP h0 h1 hv]

include hP in
/-- Nondegeneracy makes the component span genuinely two-dimensional. -/
theorem searchSpace_finrank_eq_two (h0 : 0 < successWeight P (ψ₀ : E))
    (h1 : successWeight P (ψ₀ : E) < 1) :
    Module.finrank ℂ (searchSpace ψ₀ P) = 2 := by
  rw [← range_embed ψ₀ h0 h1,
    LinearMap.finrank_range_of_inj (embedding_injective ψ₀ hP h0 h1)]
  exact finrank_euclideanSpace_fin

end
end QFixLean.FixedPoint.Reduction
