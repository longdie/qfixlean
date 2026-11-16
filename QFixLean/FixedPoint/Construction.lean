module

public import QFixLean.FixedPoint.PhaseSequence

/-!
# Explicit, countable bit-oracle constructions

P14 v2, Figure 2 and the paragraph defining `L-1=2ℓ` queries. Products are
in operator order (right child first). The syntax retains every primitive,
including zero-angle phases; counts belong to this unoptimized construction.
The target bit-flip is a supplied query primitive, not a free evaluation of
its defining projection. Preparation and its adjoint are charged separately
and are assumed to contain no target queries in the basic model.
-/

@[expose] public section

namespace QFixLean.FixedPoint

/-- Separately charged resource categories. -/
inductive QueryResource
  | oracle | prepare | unprepare | referencePhase | ancillaPhase
  deriving DecidableEq, Repr

/-- Physical primitives used to implement one generalized iterate. -/
inductive QueryInstruction
  | oracle
  | prepare
  | unprepare
  | referencePhase (angle : ℝ)
  | ancillaPhase (angle : ℝ)

namespace QueryInstruction

def resource : QueryInstruction → QueryResource
  | .oracle => .oracle
  | .prepare => .prepare
  | .unprepare => .unprepare
  | .referencePhase _ => .referencePhase
  | .ancillaPhase _ => .ancillaPhase

end QueryInstruction

/-- A minimal product expression; the right factor acts first. -/
inductive QueryConstruction
  | skip
  | gate (instruction : QueryInstruction)
  | mul (left right : QueryConstruction)

namespace QueryConstruction

instance : Mul QueryConstruction := ⟨.mul⟩

/-- Recursive occurrence count in the same expression that will be executed. -/
def count (kind : QueryResource) : QueryConstruction → ℕ
  | .skip => 0
  | .gate instruction => if kind = instruction.resource then 1 else 0
  | .mul left right => count kind left + count kind right

abbrev queries (C : QueryConstruction) := C.count .oracle
abbrev prepareCalls (C : QueryConstruction) := C.count .prepare
abbrev unprepareCalls (C : QueryConstruction) := C.count .unprepare
abbrev referencePhases (C : QueryConstruction) := C.count .referencePhase
abbrev ancillaPhases (C : QueryConstruction) := C.count .ancillaPhase

@[simp] theorem count_skip (kind : QueryResource) : count kind .skip = 0 := rfl
@[simp] theorem count_gate (kind : QueryResource) (instruction : QueryInstruction) :
    count kind (.gate instruction) = if kind = instruction.resource then 1 else 0 := rfl
@[simp] theorem count_mul (kind : QueryResource) (left right : QueryConstruction) :
    count kind (left * right) = count kind left + count kind right := rfl

/-- Target phase: query, ancilla diagonal phase, then the same query again. -/
def targetPhase (α : ℝ) : QueryConstruction :=
  .gate .oracle * .gate (.ancillaPhase α) * .gate .oracle

/-- Fixed prepared-source phase: A†, reference-state phase, then A. -/
def sourcePhase (β : ℝ) : QueryConstruction :=
  .gate .prepare * .gate (.referencePhase β) * .gate .unprepare

/-- P24 order: target first, source second, retaining the exact global phase. -/
def step (α β : ℝ) : QueryConstruction := sourcePhase β * targetPhase α

/-- Compile a time-ordered list using the same source preparation at all steps. -/
def compile : List (ℝ × ℝ) → QueryConstruction
  | [] => .skip
  | p :: ps => compile ps * step p.1 p.2

/-- Include the initial preparation from the reference state. -/
def complete (ps : List (ℝ × ℝ)) : QueryConstruction := compile ps * .gate .prepare

@[simp] theorem compile_nil : compile [] = .skip := rfl
@[simp] theorem compile_cons (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    compile (p :: ps) = compile ps * step p.1 p.2 := rfl

theorem compile_singleton (α β : ℝ) : compile [(α, β)] = .skip * step α β := rfl

theorem compile_pair (α₁ β₁ α₂ β₂ : ℝ) :
    compile [(α₁, β₁), (α₂, β₂)] = (.skip * step α₂ β₂) * step α₁ β₁ := rfl

/-- Counts for a general list, before choosing explicit phases. -/
theorem compile_counts (ps : List (ℝ × ℝ)) :
    (compile ps).queries = 2 * ps.length ∧
    (compile ps).prepareCalls = ps.length ∧
    (compile ps).unprepareCalls = ps.length ∧
    (compile ps).referencePhases = ps.length ∧
    (compile ps).ancillaPhases = ps.length := by
  induction ps with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons p ps ih =>
    rcases ih with ⟨ho, hp, hu, hr, ha⟩
    dsimp only [queries, prepareCalls, unprepareCalls, referencePhases, ancillaPhases] at *
    simp only [compile_cons, count_mul, step, sourcePhase, targetPhase,
      count_gate, QueryInstruction.resource, List.length_cons] at *
    simp only [ite_true, ite_false, reduceCtorEq, ho, hp, hu, hr, ha]
    simp [Nat.mul_add]

/-- Initial preparation adds one A call, with all search operations unchanged. -/
theorem complete_counts (ps : List (ℝ × ℝ)) :
    (complete ps).queries = 2 * ps.length ∧
    (complete ps).prepareCalls = ps.length + 1 ∧
    (complete ps).unprepareCalls = ps.length ∧
    (complete ps).referencePhases = ps.length ∧
    (complete ps).ancillaPhases = ps.length := by
  rcases compile_counts ps with ⟨ho, hp, hu, hr, ha⟩
  dsimp only [queries, prepareCalls, unprepareCalls, referencePhases, ancillaPhases] at *
  simp [complete, QueryInstruction.resource, ho, hp, hu, hr, ha]

end QueryConstruction
end QFixLean.FixedPoint
