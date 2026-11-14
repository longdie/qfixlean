module

public import QFixLean.Basic.State
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Unitary evolution of pure states

Operators use `E →L[ℂ] E`, and unitary operators use Mathlib's native `unitary`
group. Its multiplication composes right to left, `star` is the adjoint, and
`Unitary.star_eq_inv` identifies the adjoint with the inverse. Identity,
composition and adjoint therefore stay in the same unitary type.

Mathlib's `Unitary.norm_map` and `Unitary.inner_map_map` provide norm and inner
product preservation for general vectors. This file transports that action to
`PureState`, without adding vector operations to normalized states.
-/

@[expose] public section

namespace QFixLean.PureState

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Apply a unitary operator, carrying its norm preservation into the state proof. -/
def map (U : unitary (E →L[ℂ] E)) (ψ : PureState E) : PureState E :=
  ⟨(U : E →L[ℂ] E) (ψ : E), (Unitary.norm_map U _).trans ψ.normalized⟩

@[simp]
theorem coe_map (U : unitary (E →L[ℂ] E)) (ψ : PureState E) :
    (map U ψ : E) = (U : E →L[ℂ] E) (ψ : E) := rfl

@[simp]
theorem map_one (ψ : PureState E) : map 1 ψ = ψ := by
  apply ext
  rfl

/-- The right factor acts first, matching operator multiplication. -/
theorem map_mul (U V : unitary (E →L[ℂ] E)) (ψ : PureState E) :
    map (U * V) ψ = map U (map V ψ) := by
  apply ext
  rfl

/-- Unitary evolution preserves the complex inner product of two pure states. -/
theorem inner_map_map (U : unitary (E →L[ℂ] E)) (ψ φ : PureState E) :
    inner ℂ (map U ψ : E) (map U φ : E) = inner ℂ (ψ : E) (φ : E) :=
  Unitary.inner_map_map U _ _

/-- Applying the adjoint after a unitary recovers the original state. -/
@[simp]
theorem map_star_map (U : unitary (E →L[ℂ] E)) (ψ : PureState E) :
    map (star U) (map U ψ) = ψ := by
  rw [← map_mul, Unitary.star_mul_self, map_one]

/-- Applying a unitary after its adjoint also recovers the original state. -/
@[simp]
theorem map_map_star (U : unitary (E →L[ℂ] E)) (ψ : PureState E) :
    map U (map (star U) ψ) = ψ := by
  rw [← map_mul, Unitary.mul_star_self, map_one]

/-- The inverse action agrees with the adjoint action. -/
theorem map_inv (U : unitary (E →L[ℂ] E)) (ψ : PureState E) :
    map U⁻¹ ψ = map (star U) ψ := rfl

/-- The adjoint reverses the order of a composed evolution. -/
theorem map_star_mul (U V : unitary (E →L[ℂ] E)) (ψ : PureState E) :
    map (star (U * V)) ψ = map (star V) (map (star U) ψ) := by
  rw [star_mul, map_mul]

end
end QFixLean.PureState
