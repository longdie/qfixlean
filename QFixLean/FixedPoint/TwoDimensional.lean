module

public import QFixLean.Basic.PhaseRotation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Two-dimensional matrices in bad, good coordinate order

The matrices here are scalar algebra. `Reduction` proves their connection to
actual Hilbert-space evolution. P24 v3, Section 3.2, gives the reflection and
phase factorization; its global factor is retained exactly.
-/

@[expose] public section

namespace QFixLean.FixedPoint.TwoDimensional

noncomputable section

abbrev Coord := EuclideanSpace ℂ (Fin 2)
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def applyMatrix (M : Mat) (v : Coord) : Coord := WithLp.toLp 2 (M.mulVec v)

def initial (x y : ℝ) : Coord := WithLp.toLp 2 ![(x : ℂ), (y : ℂ)]

def targetProjection : Mat := !![0, 0; 0, 1]

def sourceProjection (x y : ℝ) : Mat :=
  !![(x : ℂ)^2, (x : ℂ)*(y : ℂ); (x : ℂ)*(y : ℂ), (y : ℂ)^2]

def targetMatrix (α : ℝ) : Mat := !![1, 0; 0, phaseFactor α]

def sourceMatrix (x y β : ℝ) : Mat := 1 + (phaseFactor β - 1) • sourceProjection x y

def iterateMatrix (x y α β : ℝ) : Mat := sourceMatrix x y β * targetMatrix α

def sequenceMatrix (x y : ℝ) : List (ℝ × ℝ) → Mat
  | [] => 1
  | p :: ps => sequenceMatrix x y ps * iterateMatrix x y p.1 p.2

def reflectionMatrix (x y : ℝ) : Mat := !![(x : ℂ), (y : ℂ); (y : ℂ), -(x : ℂ)]

def mtMatrix (φ : ℝ) : Mat := !![1, 0; 0, phaseFactor (-φ)]

@[simp]
theorem applyMatrix_apply (M : Mat) (v : Coord) (i : Fin 2) :
    applyMatrix M v i = M i 0 * v 0 + M i 1 * v 1 := by
  simp [applyMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp]
theorem initial_zero (x y : ℝ) : initial x y 0 = (x : ℂ) := rfl

@[simp]
theorem initial_one (x y : ℝ) : initial x y 1 = (y : ℂ) := rfl

@[simp]
theorem applyMatrix_one (v : Coord) : applyMatrix 1 v = v := by
  ext i
  fin_cases i <;> simp [applyMatrix_apply]

theorem applyMatrix_mul (M N : Mat) (v : Coord) :
    applyMatrix (M * N) v = applyMatrix M (applyMatrix N v) := by
  ext i
  simp [applyMatrix, Matrix.mulVec_mulVec]

theorem applyMatrix_add (M N : Mat) (v : Coord) :
    applyMatrix (M + N) v = applyMatrix M v + applyMatrix N v := by
  ext i
  simp [applyMatrix_apply]
  ring

theorem applyMatrix_smul (c : ℂ) (M : Mat) (v : Coord) :
    applyMatrix (c • M) v = c • applyMatrix M v := by
  ext i
  simp [applyMatrix_apply]
  ring

theorem applyMatrix_vector_add (M : Mat) (v w : Coord) :
    applyMatrix M (v + w) = applyMatrix M v + applyMatrix M w := by
  ext i
  simp [applyMatrix_apply]
  ring

theorem applyMatrix_vector_smul (M : Mat) (c : ℂ) (v : Coord) :
    applyMatrix M (c • v) = c • applyMatrix M v := by
  ext i
  simp [applyMatrix_apply]
  ring

@[simp]
theorem sequenceMatrix_nil (x y : ℝ) : sequenceMatrix x y [] = 1 := rfl

@[simp]
theorem sequenceMatrix_cons (x y : ℝ) (p : ℝ × ℝ) (ps : List (ℝ × ℝ)) :
    sequenceMatrix x y (p :: ps) = sequenceMatrix x y ps * iterateMatrix x y p.1 p.2 := rfl

@[simp]
theorem sequenceMatrix_singleton (x y : ℝ) (p : ℝ × ℝ) :
    sequenceMatrix x y [p] = iterateMatrix x y p.1 p.2 := by simp

theorem sequenceMatrix_append (x y : ℝ) (ps qs : List (ℝ × ℝ)) :
    sequenceMatrix x y (ps ++ qs) = sequenceMatrix x y qs * sequenceMatrix x y ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih, Matrix.mul_assoc]

theorem sourceMatrix_entries (x y β : ℝ) :
    sourceMatrix x y β =
      !![1 + (phaseFactor β - 1) * (x : ℂ)^2,
          (phaseFactor β - 1) * (x : ℂ) * (y : ℂ);
         (phaseFactor β - 1) * (x : ℂ) * (y : ℂ),
          1 + (phaseFactor β - 1) * (y : ℂ)^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceMatrix, sourceProjection] <;> ring

theorem iterateMatrix_entries (x y α β : ℝ) :
    iterateMatrix x y α β =
      !![1 + (phaseFactor β - 1) * (x : ℂ)^2,
          (phaseFactor β - 1) * (x : ℂ) * (y : ℂ) * phaseFactor α;
         (phaseFactor β - 1) * (x : ℂ) * (y : ℂ),
          (1 + (phaseFactor β - 1) * (y : ℂ)^2) * phaseFactor α] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iterateMatrix, sourceMatrix_entries, targetMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem star_sourceProjection (x y : ℝ) : star (sourceProjection x y) = sourceProjection x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceProjection, Matrix.star_apply]

theorem sourceProjection_sq {x y : ℝ} (hxy : x^2 + y^2 = 1) :
    sourceProjection x y * sourceProjection x y = sourceProjection x y := by
  have h : (x : ℂ)^2 + (y : ℂ)^2 = 1 := by exact_mod_cast hxy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceProjection, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (x : ℂ)^2 * h
  · linear_combination (x : ℂ)*(y : ℂ) * h
  · linear_combination (x : ℂ)*(y : ℂ) * h
  · linear_combination (y : ℂ)^2 * h

theorem star_reflectionMatrix (x y : ℝ) :
    star (reflectionMatrix x y) = reflectionMatrix x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectionMatrix, Matrix.star_apply]

theorem reflectionMatrix_sq {x y : ℝ} (hxy : x^2 + y^2 = 1) :
    reflectionMatrix x y * reflectionMatrix x y = 1 := by
  have h : (x : ℂ)^2 + (y : ℂ)^2 = 1 := by exact_mod_cast hxy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem reflectionMatrix_initial (x y : ℝ) :
    applyMatrix (reflectionMatrix x y) (initial 1 0) = initial x y := by
  ext i
  fin_cases i <;> simp [applyMatrix_apply, reflectionMatrix]

theorem iterateMatrix_factorization {x y : ℝ} (hxy : x^2 + y^2 = 1) (α β : ℝ) :
    iterateMatrix x y α β = phaseFactor β •
      (reflectionMatrix x y * mtMatrix β * reflectionMatrix x y * mtMatrix (-α)) := by
  have h : (x : ℂ)^2 + (y : ℂ)^2 = 1 := by exact_mod_cast hxy
  have hz : phaseFactor β * phaseFactor (-β) = 1 := by
    rw [← phaseFactor_add, add_neg_cancel, phaseFactor_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iterateMatrix_entries, reflectionMatrix, mtMatrix]
  · linear_combination -h - (y : ℂ)^2 * hz
  · linear_combination (x : ℂ)*(y : ℂ) * phaseFactor α * hz
  · linear_combination (x : ℂ)*(y : ℂ) * hz
  · linear_combination -phaseFactor α * h - (x : ℂ)^2 * phaseFactor α * hz


theorem reflectionMatrix_mem_unitary {x y : ℝ} (hxy : x^2 + y^2 = 1) :
    reflectionMatrix x y ∈ unitary Mat := by
  rw [Unitary.mem_iff, star_reflectionMatrix, reflectionMatrix_sq hxy]
  exact ⟨rfl, rfl⟩

theorem targetMatrix_mem_unitary (α : ℝ) : targetMatrix α ∈ unitary Mat := by
  have hz : starRingEnd ℂ (phaseFactor α) * phaseFactor α = 1 :=
    phaseFactor_star_mul_self α
  have hz' : phaseFactor α * starRingEnd ℂ (phaseFactor α) = 1 := by
    rw [mul_comm]
    exact hz
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [targetMatrix, Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two,
      hz, hz']

theorem mtMatrix_mem_unitary (φ : ℝ) : mtMatrix φ ∈ unitary Mat :=
  targetMatrix_mem_unitary (-φ)

theorem iterateMatrix_mem_unitary {x y : ℝ} (hxy : x^2 + y^2 = 1) (α β : ℝ) :
    iterateMatrix x y α β ∈ unitary Mat := by
  rw [iterateMatrix_factorization hxy]
  apply Unitary.smul_mem_of_mem
  · rw [Unitary.mem_iff]
    exact ⟨phaseFactor_star_mul_self β,
      by simpa [mul_comm] using phaseFactor_star_mul_self β⟩
  · exact (unitary Mat).mul_mem
      ((unitary Mat).mul_mem
        ((unitary Mat).mul_mem (reflectionMatrix_mem_unitary hxy) (mtMatrix_mem_unitary β))
        (reflectionMatrix_mem_unitary hxy)) (mtMatrix_mem_unitary (-α))

theorem sequenceMatrix_mem_unitary {x y : ℝ} (hxy : x^2 + y^2 = 1)
    (ps : List (ℝ × ℝ)) : sequenceMatrix x y ps ∈ unitary Mat := by
  induction ps with
  | nil => exact (unitary Mat).one_mem
  | cons p ps ih =>
    exact (unitary Mat).mul_mem ih (iterateMatrix_mem_unitary hxy p.1 p.2)

end
end QFixLean.FixedPoint.TwoDimensional
