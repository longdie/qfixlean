module

public import QFixLean.FixedPoint.Interleaved
public import QFixLean.FixedPoint.PhaseConventions
public import QFixLean.Polynomial.QuasiChebyshev
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Explicit phase schedules and the P14/P24 convention bridge

P14, arXiv:1409.3305v2, explicit phase formula (PDF (11), HTML (14)); P24,
arXiv:2403.02057v3, Sections 2 and 3.3. The arccot branch is
`π/2 - arctan`; angles differing by a full turn induce the same operator.
Lists are in time order and use the same fixed source state throughout.
-/

@[expose] public section

namespace QFixLean.FixedPoint.ExplicitPhases

noncomputable section

/-- P24 target/source pair at the one-based step `j`. -/
def pair (ℓ : ℕ) (γ : ℝ) (j : ℕ) : ℝ × ℝ :=
  (Real.pi - QuasiChebyshev.angle (2 * ℓ + 1) γ (2 * j - 1),
    QuasiChebyshev.angle (2 * ℓ + 1) γ (2 * j) - Real.pi)

/-- Explicit P24 phases, with `j=1,...,ℓ`, in execution order. -/
def schedule (ℓ : ℕ) (γ : ℝ) : List (ℝ × ℝ) :=
  (List.range ℓ).map (fun i => pair ℓ γ (i + 1))

@[simp] theorem schedule_zero (γ : ℝ) : schedule 0 γ = [] := rfl

@[simp] theorem schedule_length (ℓ : ℕ) (γ : ℝ) : (schedule ℓ γ).length = ℓ := by
  simp [schedule]

/-- Extracting recurrence angles from concatenated physical steps preserves order. -/
theorem angles_append (xs ys : List (ℝ × ℝ)) :
    AmplitudeRecurrence.angles (xs ++ ys) =
      AmplitudeRecurrence.angles xs ++ AmplitudeRecurrence.angles ys := by
  simp [AmplitudeRecurrence.angles, AmplitudeRecurrence.rawAngles,
    List.flatMap_append, List.map_append]

private theorem angles_prefix (ℓ n : ℕ) (γ : ℝ) :
    AmplitudeRecurrence.angles ((List.range n).map (fun i => pair ℓ γ (i + 1))) =
      QuasiChebyshev.specifiedPrefix (2 * ℓ + 1) γ (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, angles_append, ih]
    have hi : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have hj : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    simp only [List.map_cons, List.map_nil, AmplitudeRecurrence.angles_cons,
      AmplitudeRecurrence.angles_nil, pair]
    rw [hi, hj, QuasiChebyshev.specifiedPrefix_succ,
      QuasiChebyshev.specifiedPrefix_succ]
    simp only [List.append_assoc, List.singleton_append]
    congr 2 <;> ring_nf

/-- The very same physical phase list supplies all `2ℓ` M16 recurrence angles. -/
theorem angles_schedule (ℓ : ℕ) (γ : ℝ) :
    AmplitudeRecurrence.angles (schedule ℓ γ) = QuasiChebyshev.terminalPhases ℓ γ :=
  angles_prefix ℓ ℓ γ

/-- The `(0,π)` inverse-cotangent branch, total at zero. -/
def arccot (t : ℝ) : ℝ := Real.pi / 2 - Real.arctan t

/-- The selected inverse-cotangent representative lies strictly between zero and π. -/
theorem arccot_mem_Ioo (t : ℝ) : arccot t ∈ Set.Ioo 0 Real.pi := by
  constructor
  · dsimp [arccot]
    linarith [Real.arctan_lt_pi_div_two t]
  · dsimp [arccot]
    linarith [Real.neg_pi_div_two_lt_arctan t]

/-- P14's source parameter `2 arccot(sqrt(1-γ²) tan(2πj/L))`. -/
def p14Source (ℓ : ℕ) (γ : ℝ) (j : ℕ) : ℝ :=
  2 * arccot (QuasiChebyshev.tangent (2 * ℓ + 1) γ (2 * j))

theorem p14Source_eq (ℓ : ℕ) (γ : ℝ) (j : ℕ) :
    p14Source ℓ γ j = Real.pi - QuasiChebyshev.angle (2 * ℓ + 1) γ (2 * j) := by
  simp only [p14Source, arccot, QuasiChebyshev.angle]
  ring

/-- P14's phase matching `B_j=-A_(ℓ-j+1)`, with its own parameter order. -/
def p14Pair (ℓ : ℕ) (γ : ℝ) (j : ℕ) : ℝ × ℝ :=
  (p14Source ℓ γ j, -p14Source ℓ γ (ℓ - j + 1))

/-- P14's explicit list, without reversing execution time. -/
def p14Schedule (ℓ : ℕ) (γ : ℝ) : List (ℝ × ℝ) :=
  (List.range ℓ).map (fun i => p14Pair ℓ γ (i + 1))

@[simp] theorem p14Schedule_zero (γ : ℝ) : p14Schedule 0 γ = [] := rfl

@[simp] theorem p14Schedule_length (ℓ : ℕ) (γ : ℝ) :
    (p14Schedule ℓ γ).length = ℓ := by simp [p14Schedule]

/-- The reflected odd index negates the specified angle, including `γ=1`. -/
theorem angle_reflection (ℓ : ℕ) (γ : ℝ) (n : ℕ) (hn : n ≤ 2 * ℓ + 1) :
    QuasiChebyshev.angle (2 * ℓ + 1) γ (2 * ℓ + 1 - n) =
      -QuasiChebyshev.angle (2 * ℓ + 1) γ n := by
  rw [QuasiChebyshev.angle,
    QuasiChebyshev.tangent_reflection (by omega) hn, Real.arctan_neg]
  simp only [QuasiChebyshev.angle]
  ring

/-- P14's conversion agrees in source angle and differs by one turn in target. -/
theorem p14Pair_conversion (ℓ : ℕ) (γ : ℝ) (j : ℕ) (hj : 1 ≤ j) (hjℓ : j ≤ ℓ) :
    p14ToP24 (p14Pair ℓ γ j) = ((pair ℓ γ j).1 - 2 * Real.pi, (pair ℓ γ j).2) := by
  have hidx : 2 * (ℓ - j + 1) = 2 * ℓ + 1 - (2 * j - 1) := by omega
  have hn : 2 * j - 1 ≤ 2 * ℓ + 1 := by omega
  simp only [p14ToP24, p14Pair, p14Source_eq, pair, hidx, angle_reflection ℓ γ _ hn]
  congr 1 <;> ring_nf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Full turns change the angle representative, not its phase factor. -/
theorem phaseFactor_sub_two_pi (θ : ℝ) : phaseFactor (θ - 2 * Real.pi) = phaseFactor θ := by
  have hperiod : phaseFactor (-(2 * Real.pi)) = 1 := by
    rw [show -(2 * Real.pi) = -Real.pi + -Real.pi by ring, phaseFactor_add]
    simp [phaseFactor_neg]
  rw [sub_eq_add_neg, phaseFactor_add, hperiod, mul_one]

omit [CompleteSpace E] in
/-- Operator-level periodicity applies to general target projections. -/
theorem phaseRotation_sub_two_pi (P : E →L[ℂ] E) (θ : ℝ) :
    phaseRotation P (θ - 2 * Real.pi) = phaseRotation P θ := by
  simp only [phaseRotation, phaseFactor_sub_two_pi]

/-- One converted explicit pair agrees as an actual P24 iterate. -/
theorem iterate_p14Pair_conversion (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) (j : ℕ)
    (hj : 1 ≤ j) (hjℓ : j ≤ ℓ) :
    iterate ψ₀ hP (p14ToP24 (p14Pair ℓ γ j)).1
      (p14ToP24 (p14Pair ℓ γ j)).2 =
      iterate ψ₀ hP (pair ℓ γ j).1 (pair ℓ γ j).2 := by
  rw [p14Pair_conversion ℓ γ j hj hjℓ]
  apply Subtype.ext
  simp only [coe_iterate, phaseRotation_sub_two_pi]

/-- The whole converted schedule executes the same operator, with no time reversal. -/
theorem execute_p14Schedule_conversion (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    execute ψ₀ hP ((p14Schedule ℓ γ).map p14ToP24) = execute ψ₀ hP (schedule ℓ γ) := by
  have hprefix : ∀ n, n ≤ ℓ →
      execute ψ₀ hP (((List.range n).map (fun i => p14Pair ℓ γ (i + 1))).map p14ToP24) =
        execute ψ₀ hP ((List.range n).map (fun i => pair ℓ γ (i + 1))) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.map_append, List.map_append,
        execute_append, execute_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, execute_cons, execute_nil, one_mul]
      rw [iterate_p14Pair_conversion ψ₀ hP ℓ γ (n + 1) (by omega) (by omega)]
  exact hprefix ℓ le_rfl

/-- Exact P14/P24 explicit-execution equality, retaining `(-1)^ℓ`. -/
theorem p14Execute_schedule_coe (ψ₀ : PureState E) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (ℓ : ℕ) (γ : ℝ) :
    (p14Execute ψ₀ hP (p14Schedule ℓ γ) : E →L[ℂ] E) =
      ((-1 : ℂ) ^ ℓ) • (execute ψ₀ hP (schedule ℓ γ) : E →L[ℂ] E) := by
  rw [p14Execute_coe_eq, p14Schedule_length, execute_p14Schedule_conversion]

end
end QFixLean.FixedPoint.ExplicitPhases
