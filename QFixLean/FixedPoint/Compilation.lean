module

public import QFixLean.FixedPoint.Construction
public import QFixLean.FixedPoint.Preparation
public import QFixLean.FixedPoint.Oracle

/-!
# Exact semantics of the bit-oracle compilation

The product syntax is interpreted on the full Hilbert ancilla space. Clean
input identities hold for every data vector, so the same ancilla may be reused
without assuming that intermediate data lie in the target subspace.
-/

@[expose] public section

namespace QFixLean.FixedPoint.QueryConstruction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every primitive has native-unitary semantics on the entire extended space. -/
def interpretInstruction (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    QueryInstruction → unitary (Ancilla.Space E →L[ℂ] Ancilla.Space E)
  | .oracle => Oracle.bitFlip hP
  | .prepare => Ancilla.liftUnitary A
  | .unprepare => Ancilla.liftUnitary (star A)
  | .referencePhase β =>
      Ancilla.liftUnitary (phaseRotationUnitary s₀.isStarProjection_projection β)
  | .ancillaPhase α => Oracle.ancillaPhase α

/-- Interpret the same expression traversed by the occurrence counters. -/
def interpret (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    QueryConstruction → unitary (Ancilla.Space E →L[ℂ] Ancilla.Space E)
  | .skip => 1
  | .gate instruction => interpretInstruction A s₀ hP instruction
  | .mul left right => interpret A s₀ hP left * interpret A s₀ hP right

@[simp] theorem interpret_skip (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : interpret A s₀ hP .skip = 1 := rfl

@[simp] theorem interpret_gate (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (i : QueryInstruction) :
    interpret A s₀ hP (.gate i) = interpretInstruction A s₀ hP i := rfl

@[simp] theorem interpret_mul (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (left right : QueryConstruction) :
    interpret A s₀ hP (left * right) = interpret A s₀ hP left * interpret A s₀ hP right := rfl

/-- The two-query target block restores its ancilla with exact data phase. -/
theorem interpret_targetPhase_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (α : ℝ) (v : E) :
    (interpret A s₀ hP (targetPhase α) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed v) = Ancilla.embed (phaseRotation P α v) := by
  exact Oracle.targetPhase_embed hP α v

/-- Source phase compiled in time order A†, reference phase, A. -/
theorem interpret_sourcePhase_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (β : ℝ) (v : E) :
    (interpret A s₀ hP (sourcePhase β) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed v) =
        Ancilla.embed (phaseRotation (PureState.map A s₀).projection β v) := by
  change Ancilla.lift (A : E →L[ℂ] E)
    (Ancilla.lift (phaseRotation s₀.projection β)
      (Ancilla.lift (star (A : E →L[ℂ] E)) (Ancilla.embed v))) = _
  rw [Ancilla.lift_embed, Ancilla.lift_embed, Ancilla.lift_embed,
    Preparation.phaseRotation_map]
  rfl

/-- The actual compiled iterate, with the same fixed prepared source as M12. -/
theorem interpret_step_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (α β : ℝ) (v : E) :
    (interpret A s₀ hP (step α β) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed v) =
        Ancilla.embed ((iterate (PureState.map A s₀) hP α β : E →L[ℂ] E) v) := by
  change (interpret A s₀ hP (sourcePhase β) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
    ((interpret A s₀ hP (targetPhase α) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed v)) = _
  rw [interpret_targetPhase_embed, interpret_sourcePhase_embed]
  rfl

/-- Whole-list correctness for arbitrary data inputs; induction reuses the
same clean ancilla and the same source, without a nondegeneracy condition. -/
theorem interpret_compile_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) (v : E) :
    (interpret A s₀ hP (compile ps) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed v) =
        Ancilla.embed ((execute (PureState.map A s₀) hP ps : E →L[ℂ] E) v) := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih =>
    change (interpret A s₀ hP (compile ps) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      ((interpret A s₀ hP (step p.1 p.2) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
        (Ancilla.embed v)) = _
    rw [interpret_step_embed, ih]
    rfl

/-- From the reference state, including the initial A preparation. -/
theorem interpret_complete_embed (A : unitary (E →L[ℂ] E)) (s₀ : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) :
    (interpret A s₀ hP (complete ps) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed (s₀ : E)) =
        Ancilla.embed (output (PureState.map A s₀) hP ps : E) := by
  change (interpret A s₀ hP (compile ps) : Ancilla.Space E →L[ℂ] Ancilla.Space E)
    ((Ancilla.liftUnitary A : Ancilla.Space E →L[ℂ] Ancilla.Space E)
      (Ancilla.embed (s₀ : E))) = _
  rw [Ancilla.liftUnitary_embed, interpret_compile_embed]
  rfl

end
end QFixLean.FixedPoint.QueryConstruction
