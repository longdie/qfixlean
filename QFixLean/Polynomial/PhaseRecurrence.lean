module

public import QFixLean.Basic.PhaseFactor
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Induction
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring

/-!
# General phase recurrences and their complex polynomials

The finite list contains the recurrence angles φ₁, …, φₘ, in time order.
`state x φs` stores `(aₘ, aₘ₊₁)`, starting from `(a₀,a₁) = (1,x)`.
Appending φ updates by `aₙ₊₁ = x (1 + exp(-iφ)) aₙ - exp(-iφ) aₙ₋₁`.
This is scalar algebra; its connection to actual quantum execution is proved
in the fixed-point amplitude module. No special phase choice is assumed.
-/

@[expose] public section

namespace QFixLean.PhaseRecurrence

noncomputable section

def coefficient (φ : ℝ) : ℂ := phaseFactor (-φ)

def step (x : ℂ) (st : ℂ × ℂ) (φ : ℝ) : ℂ × ℂ :=
  (st.2, x * (1 + coefficient φ) * st.2 - coefficient φ * st.1)

def state (x : ℂ) (φs : List ℝ) : ℂ × ℂ := φs.foldl (step x) (1, x)

def value (x : ℂ) (φs : List ℝ) : ℂ := (state x φs).2

def polynomialStep (st : Polynomial ℂ × Polynomial ℂ) (φ : ℝ) :
    Polynomial ℂ × Polynomial ℂ :=
  (st.2, Polynomial.C (1 + coefficient φ) * Polynomial.X * st.2 -
    Polynomial.C (coefficient φ) * st.1)

def polynomialState (φs : List ℝ) : Polynomial ℂ × Polynomial ℂ :=
  φs.foldl polynomialStep (1, Polynomial.X)

def polynomial (φs : List ℝ) : Polynomial ℂ := (polynomialState φs).2

@[simp]
theorem state_nil (x : ℂ) : state x [] = (1, x) := rfl

@[simp]
theorem value_nil (x : ℂ) : value x [] = x := rfl

theorem state_append (x : ℂ) (φs ψs : List ℝ) :
    state x (φs ++ ψs) = ψs.foldl (step x) (state x φs) := by
  simp only [state, List.foldl_append]

@[simp]
theorem state_snoc (x : ℂ) (φs : List ℝ) (φ : ℝ) :
    state x (φs ++ [φ]) = step x (state x φs) φ := by
  simp only [state_append, List.foldl_cons, List.foldl_nil]

@[simp]
theorem state_snoc_fst (x : ℂ) (φs : List ℝ) (φ : ℝ) :
    (state x (φs ++ [φ])).1 = value x φs := by
  rw [state_snoc]
  rfl

theorem value_snoc (x : ℂ) (φs : List ℝ) (φ : ℝ) :
    value x (φs ++ [φ]) =
      x * (1 + coefficient φ) * value x φs - coefficient φ * (state x φs).1 := by
  rw [value, state_snoc]
  rfl

@[simp]
theorem value_singleton (x : ℂ) (φ : ℝ) :
    value x [φ] = x * (1 + coefficient φ) * x - coefficient φ := by
  simp [value, state, step]

/-- Two successive appended angles give the ordinary second-order equation. -/
theorem value_snoc_snoc (x : ℂ) (φs : List ℝ) (φ ψ : ℝ) :
    value x (φs ++ [φ] ++ [ψ]) =
      x * (1 + coefficient ψ) * value x (φs ++ [φ]) -
        coefficient ψ * value x φs := by
  rw [value_snoc, state_snoc_fst]

@[simp]
theorem polynomialState_nil : polynomialState [] = (1, Polynomial.X) := rfl

@[simp]
theorem polynomial_nil : polynomial [] = Polynomial.X := rfl

theorem polynomialState_append (φs ψs : List ℝ) :
    polynomialState (φs ++ ψs) = ψs.foldl polynomialStep (polynomialState φs) := by
  simp only [polynomialState, List.foldl_append]

@[simp]
theorem polynomialState_snoc (φs : List ℝ) (φ : ℝ) :
    polynomialState (φs ++ [φ]) = polynomialStep (polynomialState φs) φ := by
  simp only [polynomialState_append, List.foldl_cons, List.foldl_nil]

@[simp]
theorem polynomialState_snoc_fst (φs : List ℝ) (φ : ℝ) :
    (polynomialState (φs ++ [φ])).1 = polynomial φs := by
  rw [polynomialState_snoc]
  rfl

theorem polynomial_snoc (φs : List ℝ) (φ : ℝ) :
    polynomial (φs ++ [φ]) =
      Polynomial.C (1 + coefficient φ) * Polynomial.X * polynomial φs -
        Polynomial.C (coefficient φ) * (polynomialState φs).1 := by
  rw [polynomial, polynomialState_snoc]
  rfl

theorem polynomial_snoc_snoc (φs : List ℝ) (φ ψ : ℝ) :
    polynomial (φs ++ [φ] ++ [ψ]) =
      Polynomial.C (1 + coefficient ψ) * Polynomial.X * polynomial (φs ++ [φ]) -
        Polynomial.C (coefficient ψ) * polynomial φs := by
  rw [polynomial_snoc, polynomialState_snoc_fst]

/-- Evaluation commutes with every finite recurrence step, for both stored terms. -/
theorem polynomialState_eval (x : ℂ) (φs : List ℝ) :
    ((polynomialState φs).1.eval x, (polynomialState φs).2.eval x) = state x φs := by
  induction φs using List.reverseRecOn with
  | nil => simp
  | append_singleton φs φ ih =>
    rw [polynomialState_snoc, state_snoc]
    have h₁ : (polynomialState φs).1.eval x = (state x φs).1 := congrArg Prod.fst ih
    have h₂ : (polynomialState φs).2.eval x = (state x φs).2 := congrArg Prod.snd ih
    apply Prod.ext
    · exact h₂
    · simp only [polynomialStep, step, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, h₁, h₂]
      ring

@[simp]
theorem polynomial_eval (x : ℂ) (φs : List ℝ) :
    (polynomial φs).eval x = value x φs :=
  congrArg Prod.snd (polynomialState_eval x φs)

@[simp]
theorem state_one (φs : List ℝ) : state 1 φs = (1, 1) := by
  induction φs using List.reverseRecOn with
  | nil => rfl
  | append_singleton φs φ ih =>
    rw [state_snoc, ih]
    simp [step]

@[simp]
theorem value_one (φs : List ℝ) : value 1 φs = 1 := by
  simp [value]

/-- At x=0, an even number of recurrence angles leaves the odd-index term zero. -/
theorem foldl_zero_snd (φs : List ℝ) (z : ℂ) (h : φs.length % 2 = 0) :
    (φs.foldl (step 0) (z, 0)).2 = 0 := by
  induction φs using List.twoStepInduction generalizing z with
  | nil => rfl
  | singleton φ => simp at h
  | cons_cons φ ψ φs ih =>
    have he : φs.length % 2 = 0 := by
      simp only [List.length_cons] at h
      omega
    simpa [step] using ih (-coefficient φ * z) he

theorem value_zero_of_even_length (φs : List ℝ) (h : φs.length % 2 = 0) :
    value 0 φs = 0 := foldl_zero_snd φs 1 h

theorem value_zero_of_length_eq_twice (φs : List ℝ) (n : ℕ)
    (h : φs.length = 2 * n) : value 0 φs = 0 := by
  apply value_zero_of_even_length
  omega

theorem value_zero_even (φs : List ℝ) (h : Even φs.length) : value 0 φs = 0 := by
  obtain ⟨n, hn⟩ := h
  apply value_zero_of_even_length
  omega

end
end QFixLean.PhaseRecurrence
