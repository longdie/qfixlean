module

public import QFixLean.Basic.Probability
public import QFixLean.Basic.Unitary
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# A single clean Hilbert-space ancilla

`Space E` represents `v₀ ⊗ |0⟩ + v₁ ⊗ |1⟩` with the Hilbert square-sum norm.
The ordinary product's maximum norm is used only in the continuous equivalence
that constructs maps, never as the quantum state norm.
-/

@[expose] public section

namespace QFixLean.Ancilla

noncomputable section

/-- Two data components with the Hilbert, rather than maximum, norm. -/
abbrev Space (E : Type*) := WithLp 2 (E × E)

variable {E : Type*}

/-- The two ancilla components. -/
def mk (v₀ v₁ : E) : Space E := WithLp.toLp 2 (v₀, v₁)

@[simp] theorem mk_fst (v₀ v₁ : E) : (mk v₀ v₁).fst = v₀ := rfl
@[simp] theorem mk_snd (v₀ v₁ : E) : (mk v₀ v₁).snd = v₁ := rfl

@[ext] theorem ext {x y : Space E} (h₀ : x.fst = y.fst) (h₁ : x.snd = y.snd) : x = y := by
  apply WithLp.ofLp_injective
  exact Prod.ext h₀ h₁

variable [NormedAddCommGroup E]

theorem norm_sq (x : Space E) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 x

/-- Ancilla initialized in its zero basis state. -/
def embed (v : E) : Space E := mk v 0

@[simp] theorem embed_fst (v : E) : (embed v).fst = v := rfl
@[simp] theorem embed_snd (v : E) : (embed v).snd = 0 := rfl
@[simp] theorem norm_embed (v : E) : ‖embed v‖ = ‖v‖ :=
  WithLp.norm_toLp_fst 2 E E v

variable [InnerProductSpace ℂ E]

/-- Clean initialization is a complex linear isometry. -/
def embedLI : E →ₗᵢ[ℂ] Space E where
  toFun := embed
  map_add' _ _ := by ext <;> simp [embed, mk]
  map_smul' _ _ := by ext <;> simp [embed, mk]
  norm_map' := norm_embed

@[simp] theorem embedLI_apply (v : E) : embedLI v = embed v := rfl

@[simp] theorem embed_smul (z : ℂ) (v : E) : embed (z • v) = z • embed v :=
  embedLI.map_smul z v

/-- A continuous two-by-two block operator, built through a continuous product equivalence. -/
def block (A B C D : E →L[ℂ] E) : Space E →L[ℂ] Space E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap ∘L
    ((A ∘L WithLp.fstL 2 ℂ E E + B ∘L WithLp.sndL 2 ℂ E E).prod
      (C ∘L WithLp.fstL 2 ℂ E E + D ∘L WithLp.sndL 2 ℂ E E))

@[simp] theorem block_fst (A B C D : E →L[ℂ] E) (x : Space E) :
    (block A B C D x).fst = A x.fst + B x.snd := rfl
@[simp] theorem block_snd (A B C D : E →L[ℂ] E) (x : Space E) :
    (block A B C D x).snd = C x.fst + D x.snd := rfl

/-- Apply the same data operation in both ancilla components. -/
def lift (T : E →L[ℂ] E) : Space E →L[ℂ] Space E := block T 0 0 T

@[simp] theorem lift_fst (T : E →L[ℂ] E) (x : Space E) : (lift T x).fst = T x.fst := by
  simp [lift]
@[simp] theorem lift_snd (T : E →L[ℂ] E) (x : Space E) : (lift T x).snd = T x.snd := by
  simp [lift]
@[simp] theorem lift_embed (T : E →L[ℂ] E) (v : E) : lift T (embed v) = embed (T v) := by
  ext <;> simp

@[simp] theorem lift_one : lift (1 : E →L[ℂ] E) = 1 := by ext x <;> simp
@[simp] theorem lift_zero : lift (0 : E →L[ℂ] E) = 0 := by ext x <;> simp

theorem lift_mul (S T : E →L[ℂ] E) : lift (S * T) = lift S * lift T := by
  ext x <;> simp

theorem lift_sub (S T : E →L[ℂ] E) : lift (S - T) = lift S - lift T := by
  ext x <;> simp

@[simp] theorem successWeight_embed (P : E →L[ℂ] E) (v : E) :
    successWeight (lift P) (embed v) = successWeight P v := by
  simp [successWeight]

@[simp] theorem failureWeight_embed (P : E →L[ℂ] E) (v : E) :
    failureWeight (lift P) (embed v) = failureWeight P v := by
  rw [failureWeight, ← lift_one, ← lift_sub, lift_embed, norm_embed]
  rfl

variable [CompleteSpace E]

theorem star_block (A B C D : E →L[ℂ] E) :
    star (block A B C D) = block (star A) (star C) (star B) (star D) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    block_fst, block_snd, inner_add_left, inner_add_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  abel

@[simp] theorem star_lift (T : E →L[ℂ] E) : star (lift T) = lift (star T) := by
  simp [lift, star_block]

/-- A data unitary remains unitary on the entire extended Hilbert space. -/
def liftUnitary (U : unitary (E →L[ℂ] E)) : unitary (Space E →L[ℂ] Space E) :=
  ⟨lift (U : E →L[ℂ] E), by
    rw [Unitary.mem_iff, star_lift, ← lift_mul, ← lift_mul]
    constructor
    · rw [Unitary.coe_star_mul_self, lift_one]
    · change lift ((U * star U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) = 1
      rw [Unitary.mul_star_self]
      exact lift_one⟩

@[simp] theorem coe_liftUnitary (U : unitary (E →L[ℂ] E)) :
    (liftUnitary U : Space E →L[ℂ] Space E) = lift (U : E →L[ℂ] E) := rfl

@[simp] theorem liftUnitary_embed (U : unitary (E →L[ℂ] E)) (v : E) :
    (liftUnitary U : Space E →L[ℂ] Space E) (embed v) =
      embed ((U : E →L[ℂ] E) v) := lift_embed _ _

/-- Lifting preserves orthogonal projections, without a rank assumption. -/
theorem isStarProjection_lift {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    IsStarProjection (lift P) := by
  constructor
  · show lift P * lift P = lift P
    rw [← lift_mul, hP.isIdempotentElem.eq]
  · show star (lift P) = lift P
    rw [star_lift, hP.isSelfAdjoint.star_eq]

end
end QFixLean.Ancilla
