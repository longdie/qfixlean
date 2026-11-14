module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Normalized pure states

A `PureState E` stores a vector in a complex inner-product space together with
its normalization proof. Equality is exact vector equality: global phase is
retained. General vector operations and unnormalized components use `E`.
-/

@[expose] public section

namespace QFixLean

/-- A normalized vector, with its global phase retained. -/
structure PureState (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  val : E
  normalized : ‖val‖ = 1

namespace PureState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

instance : CoeOut (PureState E) E := ⟨PureState.val⟩

/-- Two pure states are equal when their underlying vectors are equal. -/
@[ext]
theorem ext {ψ φ : PureState E} (h : (ψ : E) = (φ : E)) : ψ = φ := by
  cases ψ
  cases φ
  cases h
  rfl

theorem coe_injective : Function.Injective (fun ψ : PureState E => (ψ : E)) :=
  fun _ _ h => ext h

@[simp]
theorem norm_coe (ψ : PureState E) : ‖(ψ : E)‖ = 1 := ψ.normalized

@[simp]
theorem inner_self (ψ : PureState E) : inner ℂ (ψ : E) (ψ : E) = 1 :=
  inner_self_eq_one_of_norm_eq_one ψ.normalized

/-- A normalized state cannot be the zero vector. -/
theorem coe_ne_zero (ψ : PureState E) : (ψ : E) ≠ 0 := by
  intro h
  have hn := ψ.normalized
  rw [show ψ.val = 0 from h, norm_zero] at hn
  exact zero_ne_one hn

end PureState
end QFixLean
