module

public import QFixLean.Basic.PhaseRotation
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Generalized phase iterations with a fixed reference state

The convention is P24 v3, equations (1)–(2): the target phase α acts first,
then the source phase β. Every step uses the same reference state and target.
A list is in time order; hence the last listed step is the leftmost factor.
The search space is the span of the original bad and good components and is
invariant even when either component vanishes. No Chebyshev formula is assumed
or proved here.
-/

@[expose] public section

namespace QFixLean.FixedPoint

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- P24's generalized iteration: target α first, fixed-source β second. -/
def iterate (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) : unitary (E →L[ℂ] E) :=
  phaseRotationUnitary ψ₀.isStarProjection_projection β * phaseRotationUnitary hP α

@[simp]
theorem coe_iterate (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) : (iterate ψ₀ hP α β : E →L[ℂ] E) =
      phaseRotation ψ₀.projection β * phaseRotation P α := rfl

@[simp]
theorem iterate_zero (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    iterate ψ₀ hP 0 0 = 1 := by
  apply Subtype.ext
  simp

/-- The adjoint reverses the source/target order as well as negating angles. -/
theorem star_iterate (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) :
    (star (iterate ψ₀ hP α β) : E →L[ℂ] E) =
      phaseRotation P (-α) * phaseRotation ψ₀.projection (-β) := by
  change star (phaseRotation ψ₀.projection β * phaseRotation P α) = _
  rw [star_mul, star_phaseRotation hP.isSelfAdjoint,
    star_phaseRotation ψ₀.isStarProjection_projection.isSelfAdjoint]

/-- Time-ordered execution. The reference state does not change in the recursion. -/
def execute (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    List (ℝ × ℝ) → unitary (E →L[ℂ] E)
  | [] => 1
  | p :: ps => execute ψ₀ hP ps * iterate ψ₀ hP p.1 p.2

@[simp]
theorem execute_nil (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    execute ψ₀ hP [] = 1 := rfl

@[simp]
theorem execute_cons (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    execute ψ₀ hP (p :: ps) = execute ψ₀ hP ps * iterate ψ₀ hP p.1 p.2 := rfl

@[simp]
theorem execute_singleton (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) : execute ψ₀ hP [(α, β)] = iterate ψ₀ hP α β := by simp

theorem execute_pair (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α₁ β₁ α₂ β₂ : ℝ) : execute ψ₀ hP [(α₁, β₁), (α₂, β₂)] =
      iterate ψ₀ hP α₂ β₂ * iterate ψ₀ hP α₁ β₁ := by simp

/-- Appending later steps multiplies their execution on the left. -/
theorem execute_append (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (xs ys : List (ℝ × ℝ)) :
    execute ψ₀ hP (xs ++ ys) = execute ψ₀ hP ys * execute ψ₀ hP xs := by
  induction xs with
  | nil => simp
  | cons p ps ih => simp only [List.cons_append, execute_cons, ih, mul_assoc]

/-- The actual normalized output of this very same execution. -/
def output (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (ps : List (ℝ × ℝ)) : PureState E := PureState.map (execute ψ₀ hP ps) ψ₀

@[simp]
theorem coe_output (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (ps : List (ℝ × ℝ)) :
    (output ψ₀ hP ps : E) = (execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E) := rfl

theorem execute_normalized (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (ps : List (ℝ × ℝ)) : ‖(execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E)‖ = 1 :=
  (output ψ₀ hP ps).normalized

/-- The original bad/good span; its dimension can drop at degenerate inputs. -/
def searchSpace (ψ₀ : PureState E) (P : E →L[ℂ] E) : Submodule ℂ E :=
  Submodule.span ℂ {(1 - P) (ψ₀ : E), P (ψ₀ : E)}

omit [CompleteSpace E] in
theorem bad_mem_searchSpace (ψ₀ : PureState E) (P : E →L[ℂ] E) :
    (1 - P) (ψ₀ : E) ∈ searchSpace ψ₀ P :=
  Submodule.subset_span (by simp)

omit [CompleteSpace E] in
theorem good_mem_searchSpace (ψ₀ : PureState E) (P : E →L[ℂ] E) :
    P (ψ₀ : E) ∈ searchSpace ψ₀ P :=
  Submodule.subset_span (by simp)

omit [CompleteSpace E] in
theorem initial_mem_searchSpace (ψ₀ : PureState E) (P : E →L[ℂ] E) :
    (ψ₀ : E) ∈ searchSpace ψ₀ P := by
  have h := (searchSpace ψ₀ P).add_mem (bad_mem_searchSpace ψ₀ P)
    (good_mem_searchSpace ψ₀ P)
  simpa only [sub_apply, one_apply_eq_self, sub_add_cancel] using h

theorem good_inner_bad (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    inner ℂ (P (ψ₀ : E)) ((1 - P) (ψ₀ : E)) = 0 :=
  projection_inner_complement hP _

theorem projection_mem_searchSpace (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) {v : E} (hv : v ∈ searchSpace ψ₀ P) :
    P v ∈ searchSpace ψ₀ P := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  simpa only [map_add, map_smul, projection_complement_apply hP,
    projection_apply_self hP, smul_zero, zero_add] using
    (searchSpace ψ₀ P).smul_mem b (good_mem_searchSpace ψ₀ P)

omit [CompleteSpace E] in
theorem sourceProjection_mem_searchSpace (ψ₀ : PureState E) (P : E →L[ℂ] E)
    (v : E) : ψ₀.projection v ∈ searchSpace ψ₀ P := by
  rw [PureState.projection_apply]
  exact (searchSpace ψ₀ P).smul_mem _ (initial_mem_searchSpace ψ₀ P)

theorem targetPhase_mem_searchSpace (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) {v : E} (hv : v ∈ searchSpace ψ₀ P) (α : ℝ) :
    phaseRotation P α v ∈ searchSpace ψ₀ P := by
  rw [phaseRotation, selectivePhase_apply]
  exact (searchSpace ψ₀ P).add_mem hv
    ((searchSpace ψ₀ P).smul_mem _ (projection_mem_searchSpace ψ₀ hP hv))

omit [CompleteSpace E] in
theorem sourcePhase_mem_searchSpace (ψ₀ : PureState E) (P : E →L[ℂ] E)
    {v : E} (hv : v ∈ searchSpace ψ₀ P) (β : ℝ) :
    phaseRotation ψ₀.projection β v ∈ searchSpace ψ₀ P := by
  rw [phaseRotation, selectivePhase_apply]
  exact (searchSpace ψ₀ P).add_mem hv
    ((searchSpace ψ₀ P).smul_mem _ (sourceProjection_mem_searchSpace ψ₀ P v))

theorem iterate_mem_searchSpace (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) {v : E} (hv : v ∈ searchSpace ψ₀ P) (α β : ℝ) :
    (iterate ψ₀ hP α β : E →L[ℂ] E) v ∈ searchSpace ψ₀ P :=
  sourcePhase_mem_searchSpace ψ₀ P (targetPhase_mem_searchSpace ψ₀ hP hv α) β

theorem execute_mem_searchSpace (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) {v : E}
    (hv : v ∈ searchSpace ψ₀ P) :
    (execute ψ₀ hP ps : E →L[ℂ] E) v ∈ searchSpace ψ₀ P := by
  induction ps generalizing v with
  | nil => exact hv
  | cons p ps ih => exact ih (iterate_mem_searchSpace ψ₀ hP hv p.1 p.2)

theorem output_mem_searchSpace (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) :
    (output ψ₀ hP ps : E) ∈ searchSpace ψ₀ P :=
  execute_mem_searchSpace ψ₀ hP ps (initial_mem_searchSpace ψ₀ P)

omit [CompleteSpace E] in
/-- The original component span is at most two-dimensional, including endpoints. -/
theorem searchSpace_finrank_le_two (ψ₀ : PureState E) (P : E →L[ℂ] E) :
    Module.finrank ℂ (searchSpace ψ₀ P) ≤ 2 := by
  classical
  have h := finrank_span_le_card (R := ℂ) ({(1 - P) (ψ₀ : E), P (ψ₀ : E)} : Set E)
  apply h.trans
  simp only [Set.toFinset_insert, Set.toFinset_singleton]
  exact (Finset.card_insert_le _ _).trans (by simp)

end
end QFixLean.FixedPoint
