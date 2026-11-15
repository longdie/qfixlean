module

public import QFixLean.Polynomial.QuasiChebyshevPhases
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tangents on a finite odd cycle

The unscaled tangent and its purely imaginary multiple are the scalar factors
in P24, arXiv:2403.02057v3, §4.2.3, HTML Lemma 4.13 / PDF Lemma 9.
All cycle operations below are operations of `ZMod L`, without a primality
assumption.  Pole avoidance is proved separately from the total definitions.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

/-- The angle of the standard representative of a cyclic index. -/
def cyclicArgument (L : ℕ) (r : ZMod L) : ℝ :=
  (r.val : ℝ) * Real.pi / (L : ℝ)

/-- The unscaled tangent; the factor `sqrt (1 - γ²)` is deliberately absent. -/
def cyclicTangent (L : ℕ) (r : ZMod L) : ℝ :=
  Real.tan (cyclicArgument L r)

/-- The complex factor occurring in the cyclic product identity. -/
def cyclicZ (L : ℕ) (r : ZMod L) : ℂ :=
  Complex.I * (cyclicTangent L r : ℂ)

@[simp] theorem cyclicArgument_zero (L : ℕ) : cyclicArgument L 0 = 0 := by
  simp [cyclicArgument]

@[simp] theorem cyclicTangent_zero (L : ℕ) : cyclicTangent L 0 = 0 := by
  simp [cyclicTangent]

@[simp] theorem cyclicZ_zero (L : ℕ) : cyclicZ L 0 = 0 := by
  simp [cyclicZ]

theorem cyclic_cos_ne_zero {L : ℕ} (hL : 0 < L) (hodd : Odd L) (r : ZMod L) :
    Real.cos (cyclicArgument L r) ≠ 0 := by
  let : NeZero L := ⟨hL.ne'⟩
  exact cos_ne_zero_of_odd hL hodd r.val_lt

theorem cyclicArgument_mem {L : ℕ} (hL : 0 < L) (r : ZMod L) :
    0 ≤ cyclicArgument L r ∧ cyclicArgument L r < Real.pi := by
  let : NeZero L := ⟨hL.ne'⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : (r.val : ℝ) < L := by exact_mod_cast r.val_lt
  constructor
  · unfold cyclicArgument
    positivity
  · unfold cyclicArgument
    apply (div_lt_iff₀ hLr).2
    nlinarith [Real.pi_pos]

/-- An arbitrary integral angle differs from its representative by an integral
multiple of π.  This is also valid for negative indices. -/
theorem cyclicArgument_intCast {L : ℕ} (hL : 0 < L) (n : ℤ) :
    (n : ℝ) * Real.pi / (L : ℝ) =
      cyclicArgument L (n : ZMod L) + ((n / (L : ℤ) : ℤ) : ℝ) * Real.pi := by
  let : NeZero L := ⟨hL.ne'⟩
  have hv : (((n : ZMod L).val : ℕ) : ℝ) = ((n % (L : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast ZMod.val_intCast (n := L) n
  have hn : ((n % (L : ℤ) : ℤ) : ℝ) +
      (L : ℝ) * ((n / (L : ℤ) : ℤ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv n (L : ℤ)
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold cyclicArgument
  rw [hv]
  apply (div_eq_iff hLr).2
  rw [add_mul, div_mul_cancel₀ _ hLr]
  nlinarith [congrArg (fun x : ℝ => x * Real.pi) hn]

theorem cyclicTangent_intCast {L : ℕ} (hL : 0 < L) (n : ℤ) :
    cyclicTangent L (n : ZMod L) = Real.tan ((n : ℝ) * Real.pi / (L : ℝ)) := by
  rw [cyclicArgument_intCast hL n, Real.tan_add_int_mul_pi]
  rfl

theorem cyclicTangent_natCast {L : ℕ} (hL : 0 < L) (n : ℕ) :
    cyclicTangent L (n : ZMod L) = Real.tan ((n : ℝ) * Real.pi / (L : ℝ)) := by
  simpa only [Int.cast_natCast] using cyclicTangent_intCast hL (n : ℤ)

theorem cos_int_angle_ne_zero {L : ℕ} (hL : 0 < L) (hodd : Odd L) (n : ℤ) :
    Real.cos ((n : ℝ) * Real.pi / (L : ℝ)) ≠ 0 := by
  rw [cyclicArgument_intCast hL n, Real.cos_add_int_mul_pi]
  exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (cyclic_cos_ne_zero hL hodd _)

theorem cyclicTangent_eq_zero_iff {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (r : ZMod L) : cyclicTangent L r = 0 ↔ r = 0 := by
  constructor
  · intro hz
    rw [cyclicTangent, Real.tan_eq_sin_div_cos] at hz
    have hs := (div_eq_zero_iff.mp hz).resolve_right (cyclic_cos_ne_zero hL hodd r)
    obtain ⟨h0, hπ⟩ := cyclicArgument_mem hL r
    have ha : cyclicArgument L r = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hπ).mp hs
    have hp : (r.val : ℝ) * Real.pi = 0 := by
      have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      exact (div_eq_zero_iff.mp ha).resolve_right hLr
    have hv : r.val = 0 := by
      exact_mod_cast (mul_eq_zero.mp hp).resolve_right Real.pi_ne_zero
    exact (ZMod.val_eq_zero r).mp hv
  · rintro rfl
    simp

theorem cyclicZ_eq_zero_iff {L : ℕ} (hL : 0 < L) (hodd : Odd L) (r : ZMod L) :
    cyclicZ L r = 0 ↔ r = 0 := by
  rw [cyclicZ, mul_eq_zero]
  simp only [Complex.I_ne_zero, false_or, Complex.ofReal_eq_zero]
  exact cyclicTangent_eq_zero_iff hL hodd r

theorem cyclicTangent_injective {L : ℕ} (hL : 0 < L) (hodd : Odd L) :
    Function.Injective (cyclicTangent L) := by
  let : NeZero L := ⟨hL.ne'⟩
  intro a b hab
  have hc₁ := cyclic_cos_ne_zero hL hodd a
  have hc₂ := cyclic_cos_ne_zero hL hodd b
  rw [cyclicTangent, cyclicTangent, Real.tan_eq_sin_div_cos,
    Real.tan_eq_sin_div_cos] at hab
  have hmul := (div_eq_div_iff hc₁ hc₂).mp hab
  have hs : Real.sin (cyclicArgument L a - cyclicArgument L b) = 0 := by
    rw [Real.sin_sub]
    nlinarith [hmul]
  obtain ⟨ha0, haπ⟩ := cyclicArgument_mem hL a
  obtain ⟨hb0, hbπ⟩ := cyclicArgument_mem hL b
  have hdiff : cyclicArgument L a - cyclicArgument L b = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hs
  apply ZMod.val_injective L
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hv : (a.val : ℝ) = (b.val : ℝ) := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    exact (div_left_inj' hLr).mp (sub_eq_zero.mp hdiff)
  exact_mod_cast hv

theorem cyclicZ_injective {L : ℕ} (hL : 0 < L) (hodd : Odd L) :
    Function.Injective (cyclicZ L) := by
  intro a b hab
  apply cyclicTangent_injective hL hodd
  apply Complex.ofReal_injective
  exact mul_left_cancel₀ Complex.I_ne_zero hab

/-- A modular difference has the same tangent as the difference of the two
standard angles; no truncating natural subtraction occurs here. -/
theorem cyclicTangent_sub {L : ℕ} (hL : 0 < L) (a b : ZMod L) :
    cyclicTangent L (a - b) = Real.tan (cyclicArgument L a - cyclicArgument L b) := by
  let : NeZero L := ⟨hL.ne'⟩
  have hcast : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ZMod L) = a - b := by
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hcast, cyclicTangent_intCast hL]
  congr 1
  simp only [Int.cast_sub, Int.cast_natCast, cyclicArgument]
  ring

theorem cos_cyclicArgument_sub_ne_zero {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (a b : ZMod L) : Real.cos (cyclicArgument L a - cyclicArgument L b) ≠ 0 := by
  have harg : cyclicArgument L a - cyclicArgument L b =
      ((((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℝ) * Real.pi / (L : ℝ)) := by
    simp only [Int.cast_sub, Int.cast_natCast, cyclicArgument]
    ring
  rw [harg]
  exact cos_int_angle_ne_zero hL hodd _

theorem cyclicTangent_sub_identity {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (a b : ZMod L) :
    cyclicTangent L b - cyclicTangent L a =
      cyclicTangent L (b - a) * (1 + cyclicTangent L b * cyclicTangent L a) := by
  rw [cyclicTangent_sub hL]
  simp only [cyclicTangent, Real.tan_eq_sin_div_cos]
  field_simp [cyclic_cos_ne_zero hL hodd a, cyclic_cos_ne_zero hL hodd b,
    cos_cyclicArgument_sub_ne_zero hL hodd b a]
  rw [Real.sin_sub, Real.cos_sub]

/-- The sign in `1 - z(b)z(a)` includes the contribution `I² = -1`. -/
theorem cyclicZ_sub {L : ℕ} (hL : 0 < L) (hodd : Odd L) (a b : ZMod L) :
    cyclicZ L b - cyclicZ L a =
      cyclicZ L (b - a) * (1 - cyclicZ L b * cyclicZ L a) := by
  apply Complex.ext
  · simp [cyclicZ]
  · simpa [cyclicZ] using cyclicTangent_sub_identity hL hodd a b

theorem cyclicZ_sub_identity {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    (a b j : ZMod L) :
    cyclicZ L (b + j) - cyclicZ L (a + j) =
      cyclicZ L (b - a) * (1 - cyclicZ L (b + j) * cyclicZ L (a + j)) := by
  simpa only [add_sub_add_right_eq_sub] using cyclicZ_sub hL hodd (a + j) (b + j)

theorem cyclicZ_sub_ne_zero {L : ℕ} (hL : 0 < L) (hodd : Odd L)
    {a b : ZMod L} (hab : a ≠ b) : cyclicZ L (b - a) ≠ 0 := by
  rw [ne_eq, cyclicZ_eq_zero_iff hL hodd]
  exact sub_ne_zero.mpr hab.symm

theorem cyclicTangent_add {L : ℕ} (hL : 0 < L) (a b : ZMod L) :
    cyclicTangent L (a + b) = Real.tan (cyclicArgument L a + cyclicArgument L b) := by
  let : NeZero L := ⟨hL.ne'⟩
  have hcast : (((a.val : ℤ) + (b.val : ℤ) : ℤ) : ZMod L) = a + b := by
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hcast, cyclicTangent_intCast hL]
  congr 1
  simp only [Int.cast_add, Int.cast_natCast, cyclicArgument]
  ring

@[simp] theorem cyclicTangent_neg {L : ℕ} (hL : 0 < L) (a : ZMod L) :
    cyclicTangent L (-a) = -cyclicTangent L a := by
  simpa only [zero_sub, cyclicArgument_zero, Real.tan_neg, cyclicTangent] using
    cyclicTangent_sub hL (0 : ZMod L) a

@[simp] theorem cyclicZ_neg {L : ℕ} (hL : 0 < L) (a : ZMod L) :
    cyclicZ L (-a) = -cyclicZ L a := by
  simp [cyclicZ, cyclicTangent_neg hL]

theorem tangent_nat_periodic {L : ℕ} (hL : 0 < L) (n : ℕ) :
    Real.tan (((n + L : ℕ) : ℝ) * Real.pi / (L : ℝ)) =
      Real.tan ((n : ℝ) * Real.pi / (L : ℝ)) := by
  rw [← cyclicTangent_natCast hL (n + L), ← cyclicTangent_natCast hL n]
  simp

theorem tangent_nat_mod {L : ℕ} (hL : 0 < L) (n : ℕ) :
    Real.tan (((n % L : ℕ) : ℝ) * Real.pi / (L : ℝ)) =
      Real.tan ((n : ℝ) * Real.pi / (L : ℝ)) := by
  simpa only [cyclicTangent, cyclicArgument, ZMod.val_natCast] using
    cyclicTangent_natCast hL n

/-- The previously defined phase tangent is the scaled cyclic tangent of the
same index, including indices outside the standard interval. -/
theorem tangent_eq_scaled_cyclic {L : ℕ} (hL : 0 < L) (γ : ℝ) (n : ℕ) :
    tangent L γ n = Real.sqrt (1 - γ ^ 2) * cyclicTangent L (n : ZMod L) := by
  rw [cyclicTangent_natCast hL]
  rfl

theorem tangent_val_eq_scaled_cyclic {L : ℕ} (γ : ℝ) (r : ZMod L) :
    tangent L γ r.val = Real.sqrt (1 - γ ^ 2) * cyclicTangent L r := rfl

end
end QFixLean.QuasiChebyshev
