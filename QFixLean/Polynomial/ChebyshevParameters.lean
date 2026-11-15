module

public import QFixLean.Polynomial.ChebyshevBounds
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Standard Chebyshev parameters and scalar error models

Reference: Yoder, Low, Chuang, arXiv:1409.3305v2, equation (1) and the
following promise-interval argument. The noninteger-order notation
`T_{1/L}(1/δ)` is represented by `cosh (arcosh (1/δ) / L)`, while the
polynomial degree itself is a natural number cast to Mathlib's integer index.

The standard parameter guarantees require `0 < L` and `0 < δ < 1`.
Definitions outside that domain still have Lean values; no algorithmic
interpretation or endpoint-limit theorem is asserted there. The error models
below are scalar formulas, not the output probabilities of a constructed
phase-sequence algorithm. Their quantum use requires an explicit formula
hypothesis in `FixedPoint.Conditional`.
-/

@[expose] public section

namespace QFixLean.Chebyshev

noncomputable section

/-- The reciprocal hyperbolic parameter used in P14 v2. -/
def parameter (L : ℕ) (δ : ℝ) : ℝ :=
  1 / Real.cosh (Real.arcosh (1 / δ) / (L : ℝ))

/-- The squared real Chebyshev ratio at the initial failure amplitude. -/
def failureModel (L : ℕ) (δ lam : ℝ) : ℝ :=
  amplitude L (parameter L δ) (Real.sqrt (1 - lam)) ^ 2

/-- The complementary scalar model; its connection to an algorithm is conditional. -/
def successModel (L : ℕ) (δ lam : ℝ) : ℝ := 1 - failureModel L δ lam

theorem parameter_pos (L : ℕ) (δ : ℝ) : 0 < parameter L δ :=
  one_div_pos.mpr (Real.cosh_pos _)

theorem parameter_lt_one {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : parameter L δ < 1 := by
  have ha : 0 < Real.arcosh (1 / δ) :=
    Real.arcosh_pos ((one_lt_div hδ).2 hδ1)
  have ht : 0 < Real.arcosh (1 / δ) / (L : ℝ) := div_pos ha (Nat.cast_pos.mpr hL)
  have hc : 1 < Real.cosh (Real.arcosh (1 / δ) / (L : ℝ)) :=
    Real.one_lt_cosh.mpr ht.ne'
  exact (div_lt_one (Real.cosh_pos _)).2 hc

theorem parameter_mem_Ioo {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : parameter L δ ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨parameter_pos L δ, parameter_lt_one hL hδ hδ1⟩

/-- Exact denominator normalization, proved from the hyperbolic evaluation of T. -/
theorem denominator_parameter {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : denominator L (parameter L δ) = 1 / δ := by
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hL)
  have hcancel : (L : ℝ) * (Real.arcosh (1 / δ) / (L : ℝ)) =
      Real.arcosh (1 / δ) := by field_simp
  simp only [denominator, parameter, one_div_one_div, evalT,
    Polynomial.Chebyshev.T_real_cosh, Int.cast_natCast, hcancel]
  exact Real.cosh_arcosh (le_of_lt ((one_lt_div hδ).2 hδ1))

theorem denominator_parameter_pos {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < denominator L (parameter L δ) := by
  rw [denominator_parameter hL hδ hδ1]
  exact one_div_pos.mpr hδ

theorem denominator_parameter_ne_zero {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : denominator L (parameter L δ) ≠ 0 :=
  (denominator_parameter_pos hL hδ hδ1).ne'

/-- The ratio form equals the δ-scaled polynomial from P14's probability formula. -/
theorem amplitude_parameter {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (x : ℝ) :
    amplitude L (parameter L δ) x = δ * evalT L (x / parameter L δ) := by
  rw [amplitude, denominator_parameter hL hδ hδ1, div_eq_mul_inv, one_div, inv_inv, mul_comm]

/-- Exact translation from a success-probability threshold to an amplitude interval.
Only γ's nonnegativity is needed for this real square-root equivalence. -/
theorem promise_iff_sqrt_le {γ lam : ℝ} (hγ : 0 ≤ γ) :
    1 - γ ^ 2 ≤ lam ↔ Real.sqrt (1 - lam) ≤ γ := by
  rw [Real.sqrt_le_left hγ]
  constructor <;> intro h <;> linarith

theorem abs_amplitude_parameter_le {L : ℕ} {δ lam : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpromise : 1 - (parameter L δ) ^ 2 ≤ lam) :
    |amplitude L (parameter L δ) (Real.sqrt (1 - lam))| ≤ δ := by
  have hp := parameter_mem_Ioo hL hδ hδ1
  have hx : |Real.sqrt (1 - lam)| ≤ parameter L δ := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (promise_iff_sqrt_le hp.1.le).mp hpromise
  have h := abs_amplitude_le L hp.1 hp.2.le hx
  simpa only [denominator_parameter hL hδ hδ1, one_div_one_div] using h

theorem failureModel_mem_Icc {L : ℕ} {δ lam : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (_hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hpromise : 1 - (parameter L δ) ^ 2 ≤ lam) :
    failureModel L δ lam ∈ Set.Icc (0 : ℝ) (δ ^ 2) := by
  have ha := abs_le.mp (abs_amplitude_parameter_le hL hδ hδ1 hpromise)
  constructor
  · exact sq_nonneg _
  · unfold failureModel
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2)
      (show 0 ≤ δ + amplitude L (parameter L δ) (Real.sqrt (1 - lam)) by linarith [ha.1])]

theorem successModel_bounds {L : ℕ} {δ lam : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hpromise : 1 - (parameter L δ) ^ 2 ≤ lam) :
    successModel L δ lam ∈ Set.Icc (1 - δ ^ 2) 1 := by
  have hf := failureModel_mem_Icc hL hδ hδ1 hlam hpromise
  constructor <;> unfold successModel <;> linarith [hf.1, hf.2]

theorem failureModel_probability_mem_Icc {L : ℕ} {δ lam : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hpromise : 1 - (parameter L δ) ^ 2 ≤ lam) :
    failureModel L δ lam ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := failureModel_mem_Icc hL hδ hδ1 hlam hpromise
  refine ⟨hf.1, ?_⟩
  nlinarith [hf.2]

theorem successModel_mem_Icc {L : ℕ} {δ lam : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hpromise : 1 - (parameter L δ) ^ 2 ≤ lam) :
    successModel L δ lam ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := successModel_bounds hL hδ hδ1 hlam hpromise
  refine ⟨?_, hs.2⟩
  nlinarith [hs.1]

/-- One parameter choice guarantees the bounds uniformly above a promised lam₀.
The matching condition between L, δ and lam₀ remains explicit. -/
theorem uniform_model_bounds {L : ℕ} {δ lam₀ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hlam₀ : lam₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hmatch : 1 - (parameter L δ) ^ 2 ≤ lam₀) :
    ∀ lam ∈ Set.Icc lam₀ 1,
      |amplitude L (parameter L δ) (Real.sqrt (1 - lam))| ≤ δ ∧
      failureModel L δ lam ∈ Set.Icc (0 : ℝ) (δ ^ 2) ∧
      successModel L δ lam ∈ Set.Icc (1 - δ ^ 2) 1 ∧
      failureModel L δ lam ∈ Set.Icc (0 : ℝ) 1 ∧
      successModel L δ lam ∈ Set.Icc (0 : ℝ) 1 := by
  intro lam hlam
  have hr : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam₀.1.le.trans hlam.1, hlam.2⟩
  have hp : 1 - (parameter L δ) ^ 2 ≤ lam := hmatch.trans hlam.1
  exact ⟨abs_amplitude_parameter_le hL hδ hδ1 hp,
    failureModel_mem_Icc hL hδ hδ1 hr hp,
    successModel_bounds hL hδ hδ1 hr hp,
    failureModel_probability_mem_Icc hL hδ hδ1 hr hp,
    successModel_mem_Icc hL hδ hδ1 hr hp⟩

/-- Degree one gives γ = δ, not an amplification of the initial probability. -/
theorem parameter_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : parameter 1 δ = δ := by
  simp only [parameter, Nat.cast_one, div_one,
    Real.cosh_arcosh (le_of_lt ((one_lt_div hδ).2 hδ1)), one_div_one_div]

theorem failureModel_one_degree {δ lam : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) : failureModel 1 δ lam = 1 - lam := by
  rw [failureModel, parameter_one hδ hδ1, amplitude_one hδ.ne']
  exact Real.sq_sqrt (sub_nonneg.mpr hlam.2)

theorem successModel_one_degree {δ lam : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) : successModel 1 δ lam = lam := by
  rw [successModel, failureModel_one_degree hδ hδ1 hlam]
  ring

/-- The left promise boundary saturates the squared error tolerance. -/
theorem failureModel_at_threshold {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    failureModel L δ (1 - (parameter L δ) ^ 2) = δ ^ 2 := by
  have hp := parameter_pos L δ
  rw [failureModel, show 1 - (1 - (parameter L δ) ^ 2) =
      (parameter L δ) ^ 2 by ring, Real.sqrt_sq hp.le, amplitude_parameter hL hδ hδ1,
    div_self hp.ne', evalT_at_one, mul_one]

/-- Odd degree makes a perfectly successful input have zero scalar failure. -/
theorem failureModel_at_one_of_odd {L : ℕ} (hodd : Odd L) (δ : ℝ) :
    failureModel L δ 1 = 0 := by
  have hi : Odd (L : ℤ) := by exact_mod_cast hodd
  simp [failureModel, amplitude, evalT, Polynomial.Chebyshev.T_eval_zero_of_odd ℝ hi]

theorem successModel_at_one_of_odd {L : ℕ} (hodd : Odd L) (δ : ℝ) :
    successModel L δ 1 = 1 := by
  rw [successModel, failureModel_at_one_of_odd hodd, sub_zero]

/-- A zero-success input gives unit failure, outside the nontrivial promise interval. -/
theorem failureModel_at_zero {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : failureModel L δ 0 = 1 := by
  have hd := denominator_parameter_ne_zero hL hδ hδ1
  simp only [failureModel, sub_zero, Real.sqrt_one, amplitude]
  change (denominator L (parameter L δ) / denominator L (parameter L δ)) ^ 2 = 1
  rw [div_self hd, one_pow]

theorem zero_not_in_promise {L : ℕ} {δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ < 1) : ¬ (1 - (parameter L δ) ^ 2 ≤ 0) := by
  have hp := parameter_mem_Ioo hL hδ hδ1
  nlinarith [hp.1, hp.2]

end
end QFixLean.Chebyshev
