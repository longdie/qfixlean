module

public import QFixLean.FixedPoint.ExplicitPhases
public import QFixLean.FixedPoint.AmplitudeRecurrence
public import QFixLean.FixedPoint.Conditional
public import QFixLean.Polynomial.QuasiChebyshevIdentity
import Mathlib.Tactic.Linarith

/-!
# Correctness of the explicit fixed-point phase algorithm

P14, arXiv:1409.3305v2, success-probability and explicit phase formulas;
P24, arXiv:2403.02057v3, Sections 2 and 3.1--3.3. The same explicit
unitary execution is connected to M13's recurrence and M16's terminal
identity. M11's scalar error estimate then applies without a formula premise.
The source state and arbitrary-rank target are fixed throughout execution.
Oracle implementations, query accounting and finite degree selection are proved
in `FixedPoint.Resources`, which uses the actual output theorems here.
-/

@[expose] public section

namespace QFixLean.FixedPoint.ExplicitPhases

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The actual P24 execution applied to its fixed, prepared reference state. -/
def search (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (ℓ : ℕ) (γ : ℝ) : PureState E := output ψ₀ hP (schedule ℓ γ)

/-- P14's explicit sequence, including the sign of each generalized iterate. -/
def p14Search (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (ℓ : ℕ) (γ : ℝ) : PureState E :=
  PureState.map (p14Execute ψ₀ hP (p14Schedule ℓ γ)) ψ₀

variable (ψ₀ : PureState E) {P : E →L[ℂ] E} (hP : IsStarProjection P)

@[simp] theorem coe_search (ℓ : ℕ) (γ : ℝ) :
    (search ψ₀ hP ℓ γ : E) = (execute ψ₀ hP (schedule ℓ γ) : E →L[ℂ] E) (ψ₀ : E) := rfl

@[simp] theorem coe_p14Search (ℓ : ℕ) (γ : ℝ) :
    (p14Search ψ₀ hP ℓ γ : E) =
      (p14Execute ψ₀ hP (p14Schedule ℓ γ) : E →L[ℂ] E) (ψ₀ : E) := rfl

theorem search_normalized (ℓ : ℕ) (γ : ℝ) : ‖(search ψ₀ hP ℓ γ : E)‖ = 1 :=
  (search ψ₀ hP ℓ γ).normalized

theorem p14Search_normalized (ℓ : ℕ) (γ : ℝ) : ‖(p14Search ψ₀ hP ℓ γ : E)‖ = 1 :=
  (p14Search ψ₀ hP ℓ γ).normalized

/-- Exact vector correspondence; the sequence sign is retained. -/
theorem p14Search_eq_phase (ℓ : ℕ) (γ : ℝ) :
    (p14Search ψ₀ hP ℓ γ : E) = ((-1 : ℂ) ^ ℓ) • (search ψ₀ hP ℓ γ : E) := by
  rw [coe_p14Search, p14Execute_schedule_coe, smul_apply, coe_search]

omit [CompleteSpace E] in
/-- Scalar terminal value, before taking norms or discarding its real sign. -/
theorem outputAmplitude_schedule (P : E →L[ℂ] E) (ℓ : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    AmplitudeRecurrence.outputAmplitude ψ₀ P (schedule ℓ γ) =
      (Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) : ℂ) := by
  unfold AmplitudeRecurrence.outputAmplitude
  rw [angles_schedule]
  exact QuasiChebyshev.terminal_value_eq_amplitude ℓ hγ hγ1 _

/-- The exact failure vector of the actual P24 execution. Only this normalized
bad-direction expression requires nondegeneracy. -/
theorem search_failure_vector (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (h0 : 0 < successWeight P (ψ₀ : E)) (h1 : successWeight P (ψ₀ : E) < 1) :
    (1 - P) (search ψ₀ hP ℓ γ : E) =
      (badPhase (schedule ℓ γ) *
        (Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) : ℂ)) •
          Reduction.badDirection ψ₀ P := by
  change (1 - P) (output ψ₀ hP (schedule ℓ γ) : E) = _
  rw [AmplitudeRecurrence.output_failure_vector ψ₀ hP h0 h1, outputAmplitude_schedule ψ₀]
  all_goals assumption

/-- The P14 failure vector retains both accumulated phases. -/
theorem p14Search_failure_vector (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (h0 : 0 < successWeight P (ψ₀ : E)) (h1 : successWeight P (ψ₀ : E) < 1) :
    (1 - P) (p14Search ψ₀ hP ℓ γ : E) =
      (((-1 : ℂ) ^ ℓ * badPhase (schedule ℓ γ)) *
        (Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) : ℂ)) •
          Reduction.badDirection ψ₀ P := by
  rw [p14Search_eq_phase, map_smul, search_failure_vector ψ₀ hP ℓ hγ hγ1 h0 h1,
    smul_smul, mul_assoc]

/-- The actual output probability, for every initial success in `[0,1]`. -/
theorem search_failureWeight (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    failureWeight P (search ψ₀ hP ℓ γ : E) =
      Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) ^ 2 := by
  change failureWeight P (output ψ₀ hP (schedule ℓ γ) : E) = _
  rw [AmplitudeRecurrence.output_failureWeight ψ₀ hP,
    outputAmplitude_schedule ψ₀ P ℓ hγ hγ1, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Success and failure concern the same normalized execution. -/
theorem search_successWeight (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    successWeight P (search ψ₀ hP ℓ γ : E) =
      1 - Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) ^ 2 := by
  have hc := (search ψ₀ hP ℓ γ).successWeight_add_failureWeight hP
  rw [search_failureWeight ψ₀ hP ℓ hγ hγ1] at hc
  linarith

theorem p14Search_failureWeight (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    failureWeight P (p14Search ψ₀ hP ℓ γ : E) =
      Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) ^ 2 := by
  rw [p14Search_eq_phase, failureWeight_phase P (by simp)]
  exact search_failureWeight ψ₀ hP ℓ hγ hγ1

theorem p14Search_successWeight (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    successWeight P (p14Search ψ₀ hP ℓ γ : E) =
      1 - Chebyshev.amplitude (2 * ℓ + 1) γ (Reduction.failureAmplitude ψ₀ P) ^ 2 := by
  rw [p14Search_eq_phase, successWeight_phase P (by simp)]
  exact search_successWeight ψ₀ hP ℓ hγ hγ1

/-- Expanded paper formula for the actual P14 output, including degenerate
inputs. Both probabilities refer to the same normalized state. -/
theorem p14Search_probabilities (ℓ : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    failureWeight P (p14Search ψ₀ hP ℓ γ : E) =
      (Chebyshev.evalT (2 * ℓ + 1) (Real.sqrt (1 - successWeight P (ψ₀ : E)) / γ) /
        Chebyshev.evalT (2 * ℓ + 1) (1 / γ)) ^ 2 ∧
    successWeight P (p14Search ψ₀ hP ℓ γ : E) =
      1 - (Chebyshev.evalT (2 * ℓ + 1) (Real.sqrt (1 - successWeight P (ψ₀ : E)) / γ) /
        Chebyshev.evalT (2 * ℓ + 1) (1 / γ)) ^ 2 :=
  ⟨p14Search_failureWeight ψ₀ hP ℓ hγ hγ1,
    p14Search_successWeight ψ₀ hP ℓ hγ hγ1⟩

@[simp] theorem search_zero (γ : ℝ) : search ψ₀ hP 0 γ = ψ₀ := by
  simp [search, output]

@[simp] theorem p14Search_zero (γ : ℝ) : p14Search ψ₀ hP 0 γ = ψ₀ := by
  simp [p14Search]

/-- Completely bad inputs remain bad; the execution itself retains its phase. -/
theorem search_probabilities_of_success_zero
    (hs : successWeight P (ψ₀ : E) = 0) (ℓ : ℕ) (γ : ℝ) :
    successWeight P (search ψ₀ hP ℓ γ : E) = 0 ∧
      failureWeight P (search ψ₀ hP ℓ γ : E) = 1 :=
  execute_probabilities_of_success_zero ψ₀ hP hs (schedule ℓ γ)

theorem search_probabilities_of_success_one
    (hs : successWeight P (ψ₀ : E) = 1) (ℓ : ℕ) (γ : ℝ) :
    successWeight P (search ψ₀ hP ℓ γ : E) = 1 ∧
      failureWeight P (search ψ₀ hP ℓ γ : E) = 0 :=
  execute_probabilities_of_success_one ψ₀ hP hs (schedule ℓ γ)

theorem p14Search_probabilities_of_success_zero
    (hs : successWeight P (ψ₀ : E) = 0) (ℓ : ℕ) (γ : ℝ) :
    successWeight P (p14Search ψ₀ hP ℓ γ : E) = 0 ∧
      failureWeight P (p14Search ψ₀ hP ℓ γ : E) = 1 := by
  rw [p14Search_eq_phase, successWeight_phase P (by simp), failureWeight_phase P (by simp)]
  exact search_probabilities_of_success_zero ψ₀ hP hs ℓ γ

theorem p14Search_probabilities_of_success_one
    (hs : successWeight P (ψ₀ : E) = 1) (ℓ : ℕ) (γ : ℝ) :
    successWeight P (p14Search ψ₀ hP ℓ γ : E) = 1 ∧
      failureWeight P (p14Search ψ₀ hP ℓ γ : E) = 0 := by
  rw [p14Search_eq_phase, successWeight_phase P (by simp), failureWeight_phase P (by simp)]
  exact search_probabilities_of_success_one ψ₀ hP hs ℓ γ

/-- P24 output with the standard P14 error parameter. The phases depend only
on the chosen length and tolerance, not on the actual success probability. -/
def parameterSearch (ℓ : ℕ) (δ : ℝ) : PureState E :=
  search ψ₀ hP ℓ (Chebyshev.parameter (2 * ℓ + 1) δ)

/-- P14 output with the same standard parameter and explicit phase matching. -/
def p14ParameterSearch (ℓ : ℕ) (δ : ℝ) : PureState E :=
  p14Search ψ₀ hP ℓ (Chebyshev.parameter (2 * ℓ + 1) δ)

theorem parameterSearch_failureWeight (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    failureWeight P (parameterSearch ψ₀ hP ℓ δ : E) =
      Chebyshev.failureModel (2 * ℓ + 1) δ (successWeight P (ψ₀ : E)) := by
  have hp := Chebyshev.parameter_mem_Ioo (show 0 < 2 * ℓ + 1 by omega) hδ hδ1
  exact search_failureWeight ψ₀ hP ℓ hp.1 hp.2.le

theorem parameterSearch_successWeight (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    successWeight P (parameterSearch ψ₀ hP ℓ δ : E) =
      Chebyshev.successModel (2 * ℓ + 1) δ (successWeight P (ψ₀ : E)) := by
  have hp := Chebyshev.parameter_mem_Ioo (show 0 < 2 * ℓ + 1 by omega) hδ hδ1
  exact search_successWeight ψ₀ hP ℓ hp.1 hp.2.le

theorem p14ParameterSearch_failureWeight (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    failureWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) =
      Chebyshev.failureModel (2 * ℓ + 1) δ (successWeight P (ψ₀ : E)) := by
  have hp := Chebyshev.parameter_mem_Ioo (show 0 < 2 * ℓ + 1 by omega) hδ hδ1
  exact p14Search_failureWeight ψ₀ hP ℓ hp.1 hp.2.le

theorem p14ParameterSearch_successWeight (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    successWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) =
      Chebyshev.successModel (2 * ℓ + 1) δ (successWeight P (ψ₀ : E)) := by
  have hp := Chebyshev.parameter_mem_Ioo (show 0 < 2 * ℓ + 1 by omega) hδ hδ1
  exact p14Search_successWeight ψ₀ hP ℓ hp.1 hp.2.le

/-- Algorithmic error guarantee: the formula premise of the reusable
conditional theorem is discharged by the actual explicit execution. -/
theorem error_guarantee (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpromise : 1 - (Chebyshev.parameter (2 * ℓ + 1) δ) ^ 2 ≤
      successWeight P (ψ₀ : E)) :
    failureWeight P (parameterSearch ψ₀ hP ℓ δ : E) ≤ δ ^ 2 ∧
      1 - δ ^ 2 ≤ successWeight P (parameterSearch ψ₀ hP ℓ δ : E) :=
  conditional_error_guarantee _ (by omega) δ hδ hδ1 ψ₀ (parameterSearch ψ₀ hP ℓ δ) hP
    hpromise (parameterSearch_failureWeight ψ₀ hP ℓ hδ hδ1)

theorem p14_error_guarantee (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpromise : 1 - (Chebyshev.parameter (2 * ℓ + 1) δ) ^ 2 ≤
      successWeight P (ψ₀ : E)) :
    failureWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) ≤ δ ^ 2 ∧
      1 - δ ^ 2 ≤ successWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) :=
  conditional_error_guarantee _ (by omega) δ hδ hδ1 ψ₀ (p14ParameterSearch ψ₀ hP ℓ δ) hP
    hpromise (p14ParameterSearch_failureWeight ψ₀ hP ℓ hδ hδ1)

/-- One chosen list works uniformly for all inputs above the matched lower
bound. `FixedPoint.Parameters` discharges matching for its explicit odd selector,
and `FixedPoint.Resources` connects it to the counted bit-oracle construction. -/
theorem uniform_error_guarantee (ℓ : ℕ) {δ lam₀ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (_hlam₀ : lam₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hmatch : 1 - (Chebyshev.parameter (2 * ℓ + 1) δ) ^ 2 ≤ lam₀)
    (hinput : lam₀ ≤ successWeight P (ψ₀ : E)) :
    failureWeight P (parameterSearch ψ₀ hP ℓ δ : E) ≤ δ ^ 2 ∧
      1 - δ ^ 2 ≤ successWeight P (parameterSearch ψ₀ hP ℓ δ : E) :=
  error_guarantee ψ₀ hP ℓ hδ hδ1 (hmatch.trans hinput)

theorem p14_uniform_error_guarantee (ℓ : ℕ) {δ lam₀ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (_hlam₀ : lam₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hmatch : 1 - (Chebyshev.parameter (2 * ℓ + 1) δ) ^ 2 ≤ lam₀)
    (hinput : lam₀ ≤ successWeight P (ψ₀ : E)) :
    failureWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) ≤ δ ^ 2 ∧
      1 - δ ^ 2 ≤ successWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) :=
  p14_error_guarantee ψ₀ hP ℓ hδ hδ1 (hmatch.trans hinput)

/-- The promise boundary saturates the error bound for the actual execution. -/
theorem parameterSearch_failureWeight_at_threshold (ℓ : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hinitial : successWeight P (ψ₀ : E) =
      1 - (Chebyshev.parameter (2 * ℓ + 1) δ) ^ 2) :
    failureWeight P (parameterSearch ψ₀ hP ℓ δ : E) = δ ^ 2 := by
  rw [parameterSearch_failureWeight ψ₀ hP ℓ hδ hδ1, hinitial]
  exact Chebyshev.failureModel_at_threshold (by omega) hδ hδ1

theorem p14ParameterSearch_failureWeight_at_threshold (ℓ : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hinitial : successWeight P (ψ₀ : E) =
      1 - (Chebyshev.parameter (2 * ℓ + 1) δ) ^ 2) :
    failureWeight P (p14ParameterSearch ψ₀ hP ℓ δ : E) = δ ^ 2 := by
  rw [p14ParameterSearch_failureWeight ψ₀ hP ℓ hδ hδ1, hinitial]
  exact Chebyshev.failureModel_at_threshold (by omega) hδ hδ1

end
end QFixLean.FixedPoint.ExplicitPhases
