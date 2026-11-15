module

public import QFixLean.Basic.PhaseRotation

/-!
# Countable constructions for π/3 search

The three primitive kinds represent the supplied preparation `U`, the source
phase, and the target phase. An inverse flag distinguishes each primitive
from its adjoint. A product is written in operator order, so its right child
acts first. Adjoint reverses products and inverts every primitive.

Counts describe occurrences in an unoptimized syntax tree, rather than an
intrinsic cost of the represented operator. Each forward or inverse primitive
counts once in its own category. Preparing the supplied source itself is not
part of this model; no physical gate decomposition or bit-oracle compilation
is asserted.
-/

@[expose] public section

namespace QFixLean.PiOverThree

/-- The three separately charged kinds of primitive operations. -/
inductive Primitive
  | base
  | source
  | target
  deriving DecidableEq, Repr

/-- An unoptimized expression in signed primitives and operator products. -/
inductive Construction
  | gate (kind : Primitive) (inverse : Bool)
  | mul (left right : Construction)
  deriving DecidableEq, Repr

namespace Construction

instance : Mul Construction := ⟨Construction.mul⟩

/-- One forward call to the supplied base unitary. -/
def base : Construction := .gate .base false

/-- One positive π/3 source phase. -/
def source : Construction := .gate .source false

/-- One positive π/3 target phase. -/
def target : Construction := .gate .target false

/-- Structural adjoint: reverse products and invert each signed primitive. -/
def adjoint : Construction → Construction
  | .gate kind inverse => .gate kind (!inverse)
  | .mul left right => right.adjoint * left.adjoint

@[simp]
theorem adjoint_gate (kind : Primitive) (inverse : Bool) :
    adjoint (.gate kind inverse) = .gate kind (!inverse) := rfl

@[simp]
theorem adjoint_mul (left right : Construction) :
    (left * right).adjoint = right.adjoint * left.adjoint := rfl

@[simp]
theorem adjoint_adjoint (C : Construction) : C.adjoint.adjoint = C := by
  induction C with
  | gate kind inverse => simp [adjoint]
  | mul left right ihl ihr =>
      simp only [adjoint, ihl, ihr]
      rfl

/-- Number of forward or inverse occurrences of the selected primitive kind. -/
def count (kind : Primitive) : Construction → ℕ
  | .gate actual _ => if kind = actual then 1 else 0
  | .mul left right => count kind left + count kind right

abbrev targetQueries (C : Construction) : ℕ := count .target C
abbrev baseCalls (C : Construction) : ℕ := count .base C
abbrev sourceCalls (C : Construction) : ℕ := count .source C

@[simp]
theorem count_gate (kind actual : Primitive) (inverse : Bool) :
    count kind (.gate actual inverse) = if kind = actual then 1 else 0 := rfl

@[simp]
theorem count_base (kind : Primitive) :
    count kind base = if kind = .base then 1 else 0 := rfl

@[simp]
theorem count_source (kind : Primitive) :
    count kind source = if kind = .source then 1 else 0 := rfl

@[simp]
theorem count_target (kind : Primitive) :
    count kind target = if kind = .target then 1 else 0 := rfl

@[simp]
theorem count_mul (kind : Primitive) (left right : Construction) :
    count kind (left * right) = count kind left + count kind right := rfl

@[simp]
theorem count_adjoint (kind : Primitive) (C : Construction) :
    count kind C.adjoint = count kind C := by
  induction C with
  | gate actual inverse => rfl
  | mul left right ihl ihr => simp only [adjoint, count, ihl, ihr, Nat.add_comm]

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Positive primitive semantics; both selective phases use positive π/3. -/
def interpretPrimitive (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : Primitive → unitary (E →L[ℂ] E)
  | .base => U
  | .source => phaseRotationUnitary s.isStarProjection_projection (Real.pi / 3)
  | .target => phaseRotationUnitary hP (Real.pi / 3)

/-- Exact native-unitary semantics, retaining global phase. Products act
right to left, and an inverse primitive is interpreted by its adjoint. -/
def interpret (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : Construction → unitary (E →L[ℂ] E)
  | .gate kind inverse =>
      if inverse then star (interpretPrimitive U s hP kind) else interpretPrimitive U s hP kind
  | .mul left right => interpret U s hP left * interpret U s hP right

@[simp]
theorem interpret_base (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) : interpret U s hP base = U := rfl

@[simp]
theorem interpret_source (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    interpret U s hP source = phaseRotationUnitary s.isStarProjection_projection (Real.pi / 3) := rfl

@[simp]
theorem interpret_target (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    interpret U s hP target = phaseRotationUnitary hP (Real.pi / 3) := rfl

@[simp]
theorem interpret_mul (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (left right : Construction) :
    interpret U s hP (left * right) = interpret U s hP left * interpret U s hP right := rfl

/-- The right subconstruction executes first on the input vector. -/
theorem interpret_mul_apply (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (left right : Construction) (v : E) :
    (interpret U s hP (left * right) : E →L[ℂ] E) v =
      (interpret U s hP left : E →L[ℂ] E) ((interpret U s hP right : E →L[ℂ] E) v) := rfl

/-- Interpreting the structural inverse gives the adjoint of the entire
represented unitary, not a new primitive with an uncharged implementation. -/
@[simp]
theorem interpret_adjoint (U : unitary (E →L[ℂ] E)) (s : PureState E)
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (C : Construction) :
    interpret U s hP C.adjoint = star (interpret U s hP C) := by
  induction C with
  | gate kind inverse => cases inverse <;> simp [interpret, adjoint]
  | mul left right ihl ihr => simp only [adjoint, interpret, ihl, ihr, star_mul]

end
end Construction
end QFixLean.PiOverThree
