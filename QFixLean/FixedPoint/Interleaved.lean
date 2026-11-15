module

public import QFixLean.FixedPoint.TwoDimensional
public import QFixLean.FixedPoint.PhaseBoundary
public import QFixLean.Polynomial.PhaseRecurrence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Interleaved matrices and coupled amplitudes

P24 v3, Section 3.2, PDF equations (12)–(19). The initial `A(0)` is
retained: `rawAngles` holds only the following `2*l` angles. Lists are in
execution order. The auxiliary coefficient `b` represents coordinate `y*b`.
Elimination is polynomial algebra and uses no division or nondegeneracy.
-/

@[expose] public section

namespace QFixLean.FixedPoint.AmplitudeRecurrence

noncomputable section
open TwoDimensional

/-- Raw interleaved angles after the initial angle zero, in time order. -/
def rawAngles (ps : List (ℝ × ℝ)) : List ℝ := ps.flatMap (fun p => [-p.1, p.2])

/-- Recurrence angles: every raw angle after the initial zero is shifted by π. -/
def angles (ps : List (ℝ × ℝ)) : List ℝ := (rawAngles ps).map (fun θ => θ + Real.pi)

@[simp] theorem rawAngles_nil : rawAngles [] = [] := rfl

@[simp] theorem rawAngles_cons (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    rawAngles (p :: ps) = -p.1 :: p.2 :: rawAngles ps := rfl

@[simp] theorem angles_nil : angles [] = [] := rfl

@[simp] theorem angles_cons (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    angles (p :: ps) = (Real.pi - p.1) :: (p.2 + Real.pi) :: angles ps := by
  simp only [angles, rawAngles_cons, List.map_cons]
  rw [show -p.1 + Real.pi = Real.pi - p.1 by ring]

@[simp] theorem rawAngles_length (ps : List (ℝ × ℝ)) :
    (rawAngles ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [rawAngles_cons, List.length_cons, ih]; omega

@[simp] theorem angles_length (ps : List (ℝ × ℝ)) :
    (angles ps).length = 2 * ps.length := by simp [angles]

@[simp] theorem completeRawAngles_length (ps : List (ℝ × ℝ)) :
    (0 :: rawAngles ps).length = 2 * ps.length + 1 := by simp

/-- One interleaved factor `R Mt(θ)`. -/
def aMatrix (x y θ : ℝ) : Mat := reflectionMatrix x y * mtMatrix θ

theorem aMatrix_entries (x y θ : ℝ) :
    aMatrix x y θ =
      !![(x : ℂ), (y : ℂ) * phaseFactor (-θ);
         (y : ℂ), -(x : ℂ) * phaseFactor (-θ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aMatrix, reflectionMatrix, mtMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The head factor acts first. -/
def aSequenceMatrix (x y : ℝ) : List ℝ → Mat
  | [] => 1
  | θ :: θs => aSequenceMatrix x y θs * aMatrix x y θ

@[simp] theorem aSequenceMatrix_nil (x y : ℝ) : aSequenceMatrix x y [] = 1 := rfl

@[simp] theorem aSequenceMatrix_cons (x y θ : ℝ) (θs : List ℝ) :
    aSequenceMatrix x y (θ :: θs) = aSequenceMatrix x y θs * aMatrix x y θ := rfl

theorem aSequenceMatrix_append (x y : ℝ) (xs ys : List ℝ) :
    aSequenceMatrix x y (xs ++ ys) = aSequenceMatrix x y ys * aSequenceMatrix x y xs := by
  induction xs with
  | nil => simp
  | cons θ θs ih => simp only [List.cons_append, aSequenceMatrix_cons, ih, Matrix.mul_assoc]

theorem aMatrix_zero_initial (x y : ℝ) :
    applyMatrix (aMatrix x y 0) (initial 1 0) = initial x y := by
  ext i
  fin_cases i <;> simp [aMatrix_entries]

theorem iterateMatrix_aMatrix {x y : ℝ} (hxy : x^2 + y^2 = 1) (α β : ℝ) :
    iterateMatrix x y α β = phaseFactor β • (aMatrix x y β * aMatrix x y (-α)) := by
  rw [iterateMatrix_factorization hxy]
  simp only [aMatrix, Matrix.mul_assoc]

/-- Exact factorization of the same time-ordered phase-pair sequence. -/
theorem sequenceMatrix_factorization {x y : ℝ} (hxy : x^2 + y^2 = 1)
    (ps : List (ℝ × ℝ)) :
    sequenceMatrix x y ps = badPhase ps • aSequenceMatrix x y (rawAngles ps) := by
  induction ps with
  | nil => simp [badPhase]
  | cons p ps ih =>
    rw [sequenceMatrix_cons, ih, iterateMatrix_aMatrix hxy, rawAngles_cons]
    simp only [aSequenceMatrix_cons, badPhase, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [Matrix.mul_assoc]

/-- Coordinates associated to a coupled coefficient pair `(a,b)`. -/
def pairCoord (y : ℝ) (st : ℂ × ℂ) : Coord :=
  WithLp.toLp 2 ![st.1, (y : ℂ) * st.2]

@[simp] theorem pairCoord_zero (y : ℝ) (st : ℂ × ℂ) : pairCoord y st 0 = st.1 := rfl
@[simp] theorem pairCoord_one (y : ℝ) (st : ℂ × ℂ) : pairCoord y st 1 = (y : ℂ) * st.2 := rfl

/-- Coupled coefficient update; `b` is scaled by `y` in the actual vector. -/
def coupledStep (x : ℂ) (st : ℂ × ℂ) (θ : ℝ) : ℂ × ℂ :=
  (x * st.1 + phaseFactor (-θ) * (1-x^2) * st.2,
   st.1 - x * phaseFactor (-θ) * st.2)

/-- Coupled updates for an arbitrary starting coefficient pair. -/
def coupledRun (x : ℂ) (θs : List ℝ) (st : ℂ × ℂ) : ℂ × ℂ :=
  θs.foldl (coupledStep x) st

/-- Coupled coefficients after the complete list including the initial `A(0)`. -/
def finalCoupled (x : ℂ) (ps : List (ℝ × ℝ)) : ℂ × ℂ :=
  coupledRun x (0 :: rawAngles ps) (1,0)

@[simp] theorem coupledRun_nil (x : ℂ) (st : ℂ × ℂ) : coupledRun x [] st = st := rfl
@[simp] theorem coupledRun_cons (x : ℂ) (θ : ℝ) (θs : List ℝ) (st : ℂ × ℂ) :
    coupledRun x (θ :: θs) st = coupledRun x θs (coupledStep x st θ) := rfl

@[simp] theorem coupledStep_initial (x : ℂ) (θ : ℝ) : coupledStep x (1,0) θ = (x,1) := by
  simp [coupledStep]

/-- Appending a raw angle performs one more update on the left. -/
theorem coupledRun_snoc (x : ℂ) (θs : List ℝ) (θ : ℝ) (st : ℂ × ℂ) :
    coupledRun x (θs ++ [θ]) st = coupledStep x (coupledRun x θs st) θ := by
  simp only [coupledRun, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem finalCoupled_eq (x : ℂ) (ps : List (ℝ × ℝ)) :
    finalCoupled x ps = coupledRun x (rawAngles ps) (x,1) := by
  simp only [finalCoupled, coupledRun_cons, coupledStep_initial]

/-- The division-free cancellation used to eliminate the auxiliary component. -/
theorem coupledStep_invariant (x : ℂ) (st : ℂ × ℂ) (θ : ℝ) :
    x * (coupledStep x st θ).1 + (1-x^2) * (coupledStep x st θ).2 = st.1 := by
  simp only [coupledStep]
  ring

/-- Two coupled steps give the raw-angle second-order recurrence. -/
theorem coupledStep_secondOrder (x : ℂ) (st : ℂ × ℂ) (θ ψ : ℝ) :
    (coupledStep x (coupledStep x st θ) ψ).1 =
      x * (1-phaseFactor (-ψ)) * (coupledStep x st θ).1 +
        phaseFactor (-ψ) * st.1 := by
  simp only [coupledStep]
  ring

/-- The second-order recurrence for actual coupled coefficients of any prefix. -/
theorem coupledRun_secondOrder (x : ℂ) (θs : List ℝ) (θ ψ : ℝ)
    (st : ℂ × ℂ) :
    (coupledRun x (θs ++ [θ] ++ [ψ]) st).1 =
      x * (1-phaseFactor (-ψ)) * (coupledRun x (θs ++ [θ]) st).1 +
        phaseFactor (-ψ) * (coupledRun x θs st).1 := by
  rw [coupledRun_snoc, coupledRun_snoc]
  exact coupledStep_secondOrder x (coupledRun x θs st) θ ψ

/-- One actual matrix multiplication is exactly one coupled update. -/
theorem aMatrix_pairCoord {x y : ℝ} (hxy : x^2 + y^2 = 1)
    (θ : ℝ) (st : ℂ × ℂ) :
    applyMatrix (aMatrix x y θ) (pairCoord y st) =
      pairCoord y (coupledStep (x : ℂ) st θ) := by
  have h : (x : ℂ)^2 + (y : ℂ)^2 = 1 := by exact_mod_cast hxy
  ext i
  fin_cases i <;> simp [applyMatrix_apply, aMatrix_entries, pairCoord, coupledStep]
  · linear_combination phaseFactor (-θ) * st.2 * h
  · ring

/-- Coupled coefficients represent the entire actual interleaved matrix product. -/
theorem aSequenceMatrix_pairCoord {x y : ℝ} (hxy : x^2 + y^2 = 1)
    (θs : List ℝ) (st : ℂ × ℂ) :
    applyMatrix (aSequenceMatrix x y θs) (pairCoord y st) =
      pairCoord y (coupledRun (x : ℂ) θs st) := by
  induction θs generalizing st with
  | nil => simp
  | cons θ θs ih =>
    rw [aSequenceMatrix_cons, applyMatrix_mul, aMatrix_pairCoord hxy, ih, coupledRun_cons]

/-- Matrix-output equality including the accumulated source phase. -/
theorem sequenceMatrix_initial {x y : ℝ} (hxy : x^2 + y^2 = 1)
    (ps : List (ℝ × ℝ)) :
    applyMatrix (sequenceMatrix x y ps) (initial x y) =
      badPhase ps • pairCoord y (finalCoupled (x : ℂ) ps) := by
  rw [sequenceMatrix_factorization hxy, applyMatrix_smul]
  congr 1
  rw [← aMatrix_zero_initial x y, ← applyMatrix_mul, ← aSequenceMatrix_cons]
  have hi : initial 1 0 = pairCoord y (1,0) := by
    ext i
    fin_cases i <;> simp
  rw [hi, aSequenceMatrix_pairCoord hxy]
  rfl

/-- Shifting a raw angle by π negates its negative-exponent phase. -/
theorem phaseFactor_neg_add_pi (θ : ℝ) :
    phaseFactor (-(θ + Real.pi)) = -phaseFactor (-θ) := by
  rw [neg_add, phaseFactor_add, phaseFactor_neg Real.pi, phaseFactor_pi]
  simp

/-- The adjacent second-order pair encoded by coupled coefficients. -/
def adjacent (x : ℂ) (st : ℂ × ℂ) : ℂ × ℂ :=
  (x * st.1 + (1-x^2) * st.2, st.1)

/-- Coupled elimination is exactly the scalar second-order update. -/
theorem adjacent_coupledStep (x : ℂ) (st : ℂ × ℂ) (θ : ℝ) :
    adjacent x (coupledStep x st θ) =
      PhaseRecurrence.step x (adjacent x st) (θ + Real.pi) := by
  apply Prod.ext
  · exact coupledStep_invariant x st θ
  · simp only [adjacent, coupledStep, PhaseRecurrence.step,
      PhaseRecurrence.coefficient, phaseFactor_neg_add_pi]
    ring

/-- The scalar second-order state and the actual coupled coefficients agree. -/
theorem adjacent_coupledRun (x : ℂ) (θs : List ℝ) (st : ℂ × ℂ) :
    adjacent x (coupledRun x θs st) =
      (θs.map (fun θ => θ + Real.pi)).foldl (PhaseRecurrence.step x) (adjacent x st) := by
  induction θs generalizing st with
  | nil => rfl
  | cons θ θs ih =>
    rw [coupledRun_cons, ih, adjacent_coupledStep]
    rfl

/-- The first coupled coefficient is the proved second-order recurrence value. -/
theorem finalCoupled_fst (x : ℂ) (ps : List (ℝ × ℝ)) :
    (finalCoupled x ps).1 = PhaseRecurrence.value x (angles ps) := by
  have hi : adjacent x (x,1) = (1,x) := by
    exact Prod.ext (by simp only [adjacent]; ring) rfl
  have h := adjacent_coupledRun x (rawAngles ps) (x,1)
  rw [hi] at h
  rw [finalCoupled_eq]
  exact congrArg Prod.snd h

/-- Complete matrix output in terms of the scalar recurrence and auxiliary b. -/
theorem matrix_output_recurrence {x y : ℝ} (hxy : x^2 + y^2 = 1)
    (ps : List (ℝ × ℝ)) :
    applyMatrix (sequenceMatrix x y ps) (initial x y) =
      badPhase ps • WithLp.toLp 2
        ![PhaseRecurrence.value (x : ℂ) (angles ps),
          (y : ℂ) * (finalCoupled (x : ℂ) ps).2] := by
  rw [sequenceMatrix_initial hxy]
  congr 1
  ext i
  fin_cases i
  · exact finalCoupled_fst (x : ℂ) ps
  · rfl

end
end QFixLean.FixedPoint.AmplitudeRecurrence
