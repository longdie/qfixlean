module

public import QFixLean.FixedPoint.PhaseBoundary

/-!
# P14 and P24 phase conventions

P14 v2 uses Ss(α)=R_Q(-α), St(β)=R_P(β), G14=-Ss St.
P24 v3 uses G24(α,β)=R_Q(β) R_P(α). Thus a P14 pair maps to
(β,-α), without reversing time, and contributes a global factor -1.
The extension of P14's target phase to arbitrary-rank P is a project interface;
its restriction to the initial component span agrees with the target-direction
phase once the nondegenerate reduction is established. These statements do
not themselves identify the papers' explicit inverse-trigonometric phase
schedules; `ExplicitPhases` proves that additional correspondence.
-/

@[expose] public section

namespace QFixLean.FixedPoint

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- P14's generalized iterate, extended to an arbitrary orthogonal target. -/
def p14Iterate (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) : unitary (E →L[ℂ] E) :=
  -(phaseRotationUnitary ψ₀.isStarProjection_projection (-α)) * phaseRotationUnitary hP β

/-- The conversion swaps the parameter roles and negates the P14 source angle. -/
def p14ToP24 (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -p.1)

theorem p14Iterate_eq (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) : p14Iterate ψ₀ hP α β = -iterate ψ₀ hP β (-α) := by
  apply Subtype.ext
  change -(phaseRotation ψ₀.projection (-α)) * phaseRotation P β =
    -(phaseRotation ψ₀.projection (-α) * phaseRotation P β)
  rw [neg_mul]

@[simp]
theorem coe_p14Iterate (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (α β : ℝ) : (p14Iterate ψ₀ hP α β : E →L[ℂ] E) =
      -(phaseRotation ψ₀.projection (-α)) * phaseRotation P β := rfl

@[simp]
theorem p14Iterate_zero (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    p14Iterate ψ₀ hP 0 0 = -1 := by
  rw [p14Iterate_eq]
  simp

/-- P14 iterations in the same time order as `execute`. -/
def p14Execute (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    List (ℝ × ℝ) → unitary (E →L[ℂ] E)
  | [] => 1
  | p :: ps => p14Execute ψ₀ hP ps * p14Iterate ψ₀ hP p.1 p.2

@[simp]
theorem p14Execute_nil (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    p14Execute ψ₀ hP [] = 1 := rfl

@[simp]
theorem p14Execute_cons (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    p14Execute ψ₀ hP (p :: ps) = p14Execute ψ₀ hP ps * p14Iterate ψ₀ hP p.1 p.2 := rfl

/-- Exact operator equality: no global phase has been quotiented away. -/
theorem p14Execute_coe_eq (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) :
    (p14Execute ψ₀ hP ps : E →L[ℂ] E) =
      ((-1 : ℂ) ^ ps.length) • (execute ψ₀ hP (ps.map p14ToP24) : E →L[ℂ] E) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [p14Execute_cons, List.map_cons, execute_cons, Submonoid.coe_mul,
      p14Iterate_eq, Unitary.coe_neg, ih, p14ToP24, smul_mul_assoc, mul_neg,
      List.length_cons, pow_succ, mul_one, neg_smul]

/-- The corresponding actual vector equality retains (-1)^length. -/
theorem p14Execute_apply_eq (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) (v : E) :
    (p14Execute ψ₀ hP ps : E →L[ℂ] E) v =
      ((-1 : ℂ) ^ ps.length) •
        ((execute ψ₀ hP (ps.map p14ToP24) : E →L[ℂ] E) v) := by
  rw [p14Execute_coe_eq, smul_apply]

theorem p14Execute_successWeight (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) (v : E) :
    successWeight P ((p14Execute ψ₀ hP ps : E →L[ℂ] E) v) =
      successWeight P ((execute ψ₀ hP (ps.map p14ToP24) : E →L[ℂ] E) v) := by
  rw [p14Execute_apply_eq]
  exact successWeight_phase P (by simp) _

theorem p14Execute_failureWeight (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ps : List (ℝ × ℝ)) (v : E) :
    failureWeight P ((p14Execute ψ₀ hP ps : E →L[ℂ] E) v) =
      failureWeight P ((execute ψ₀ hP (ps.map p14ToP24) : E →L[ℂ] E) v) := by
  rw [p14Execute_apply_eq]
  exact failureWeight_phase P (by simp) _

/-- The P14 completely-bad output also retains its global sign. -/
theorem p14Execute_of_success_zero (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 0)
    (ps : List (ℝ × ℝ)) :
    (p14Execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E) =
      (((-1 : ℂ) ^ ps.length) * badPhase (ps.map p14ToP24)) • (ψ₀ : E) := by
  rw [p14Execute_apply_eq, execute_of_success_zero ψ₀ hP hs, smul_smul]

/-- The P14 completely-good output also retains its global sign. -/
theorem p14Execute_of_success_one (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (hs : successWeight P (ψ₀ : E) = 1)
    (ps : List (ℝ × ℝ)) :
    (p14Execute ψ₀ hP ps : E →L[ℂ] E) (ψ₀ : E) =
      (((-1 : ℂ) ^ ps.length) * goodPhase (ps.map p14ToP24)) • (ψ₀ : E) := by
  rw [p14Execute_apply_eq, execute_of_success_one ψ₀ hP hs, smul_smul]

end
end QFixLean.FixedPoint
