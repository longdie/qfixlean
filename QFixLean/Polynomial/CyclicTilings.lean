module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite tilings of a cycle

A domino with index `n` covers sites `n` and `n - 1`. Domino indices form a
finite set, so tile ordering creates no multiplicity; all uncovered sites
are singles. For lengths at least three, physical dominoes have unique
indices. Disjointness of the two endpoint sets excludes overlaps and also
excludes self-loop dominoes on a cycle of length one. These cases cover all
positive odd lengths used below. Translations are bijections, with no
assertion that their action is free.
-/

@[expose] public section

namespace QFixLean.QuasiChebyshev

noncomputable section

open scoped BigOperators

/-- The two endpoints of a domino, indexed by a Boolean. -/
def dominoEndpoint {L : ℕ} (n : ZMod L) (b : Bool) : ZMod L :=
  if b then n - 1 else n

/-- Legal domino indices have pairwise disjoint endpoints, including within a domino. -/
def IsCyclicTiling {L : ℕ} (D : Finset (ZMod L)) : Prop :=
  Disjoint D (D.image (· - 1))

/-- All covered sites; the complement consists of the uniquely determined singles. -/
def covered {L : ℕ} (D : Finset (ZMod L)) : Finset (ZMod L) :=
  D ∪ D.image (· - 1)

/-- The sites not covered by dominoes. -/
def singles {L : ℕ} [NeZero L] (D : Finset (ZMod L)) : Finset (ZMod L) :=
  Finset.univ \ covered D

/-- Translate every domino by the same modular displacement. -/
def rotateTilings {L : ℕ} (j : ZMod L) (D : Finset (ZMod L)) : Finset (ZMod L) :=
  D.image (· + j)

/-- Reflection of sites `n ↦ -n` sends a domino index to `1 - n`. -/
def reflectTilings {L : ℕ} (D : Finset (ZMod L)) : Finset (ZMod L) :=
  D.image (1 - ·)

@[simp] theorem isCyclicTiling_empty (L : ℕ) : IsCyclicTiling (∅ : Finset (ZMod L)) := by
  simp [IsCyclicTiling]

theorem IsCyclicTiling.ne_predecessor {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) {n m : ZMod L} (hn : n ∈ D) (hm : m ∈ D) :
    n ≠ m - 1 := by
  intro h
  exact Finset.disjoint_left.mp hD hn (Finset.mem_image.mpr ⟨m, hm, h.symm⟩)

/-- A domino never identifies its two endpoints. -/
theorem IsCyclicTiling.endpoint_ne {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) {n : ZMod L} (hn : n ∈ D) : n ≠ n - 1 :=
  hD.ne_predecessor hn hn

/-- All endpoint occurrences are distinct; none may silently be deduplicated. -/
theorem IsCyclicTiling.endpoint_injective {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) :
    Function.Injective (fun p : {n // n ∈ D} × Bool => dominoEndpoint p.1.val p.2) := by
  rintro ⟨⟨n, hn⟩, b⟩ ⟨⟨m, hm⟩, c⟩ h
  cases b <;> cases c
  · simp only [dominoEndpoint, Bool.false_eq_true, ↓reduceIte] at h
    cases h
    rfl
  · simp only [dominoEndpoint, Bool.false_eq_true, ↓reduceIte] at h
    exact (hD.ne_predecessor hn hm h).elim
  · simp only [dominoEndpoint, Bool.false_eq_true, ↓reduceIte] at h
    exact (hD.ne_predecessor hm hn h.symm).elim
  · simp only [dominoEndpoint, ↓reduceIte] at h
    have hnm : n = m := by simpa using h
    cases hnm
    rfl

/-- Covered-site cardinality is exactly twice the number of dominoes. -/
theorem IsCyclicTiling.card_covered {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) : (covered D).card = 2 * D.card := by
  rw [covered, Finset.card_union_of_disjoint hD,
    Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)]
  omega

/-- Every site is either one endpoint or a single. -/
theorem IsCyclicTiling.card_singles_add_twice {L : ℕ} [NeZero L]
    {D : Finset (ZMod L)} (hD : IsCyclicTiling D) :
    (singles D).card + 2 * D.card = L := by
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (covered D))
  simpa only [singles, hD.card_covered, Finset.card_univ, ZMod.card] using h

theorem IsCyclicTiling.twice_card_le {L : ℕ} [NeZero L]
    {D : Finset (ZMod L)} (hD : IsCyclicTiling D) : 2 * D.card ≤ L := by
  have := hD.card_singles_add_twice
  omega

theorem IsCyclicTiling.card_le_half {L : ℕ} [NeZero L]
    {D : Finset (ZMod L)} (hD : IsCyclicTiling D) (hodd : Odd L) :
    D.card ≤ (L - 1) / 2 := by
  have := hD.twice_card_le
  obtain ⟨k, hk⟩ := hodd
  omega

@[simp] theorem rotateTilings_zero {L : ℕ} (D : Finset (ZMod L)) :
    rotateTilings 0 D = D := by simp [rotateTilings]

@[simp] theorem rotateTilings_add {L : ℕ} (j k : ZMod L) (D : Finset (ZMod L)) :
    rotateTilings j (rotateTilings k D) = rotateTilings (k + j) D := by
  simp only [rotateTilings, Finset.image_image, Function.comp_def, add_assoc]

@[simp] theorem rotateTilings_card {L : ℕ} (j : ZMod L) (D : Finset (ZMod L)) :
    (rotateTilings j D).card = D.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

@[simp] theorem reflectTilings_card {L : ℕ} (D : Finset (ZMod L)) :
    (reflectTilings D).card = D.card :=
  Finset.card_image_of_injective _ (fun _ _ h => sub_right_injective h)

@[simp] theorem reflectTilings_reflect {L : ℕ} (D : Finset (ZMod L)) :
    reflectTilings (reflectTilings D) = D := by
  simp [reflectTilings, Finset.image_image]

/-- A rotation preserves non-overlap without imposing a full-length orbit. -/
theorem IsCyclicTiling.rotate {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) (j : ZMod L) : IsCyclicTiling (rotateTilings j D) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hb
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
  have : n = m - 1 := by
    apply add_right_cancel (b := j)
    simpa only [sub_add_eq_add_sub] using hab.symm
  exact hD.ne_predecessor hn hm this

/-- Reflection of domino indices is `n ↦ 1 - n`, as dictated by their endpoints. -/
theorem IsCyclicTiling.reflect {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) : IsCyclicTiling (reflectTilings D) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hb
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
  have : m = n - 1 := by
    have h : 1 - m - 1 = 1 - n := hab
    simp only [sub_sub_cancel_left] at h
    have := congrArg (fun x : ZMod L => -x) h
    simpa using this
  exact hD.ne_predecessor hm hn this

/-- Each finite set of domino indices corresponds to a single tiling. -/
def CyclicTiling (L : ℕ) := {D : Finset (ZMod L) // IsCyclicTiling D}

instance {L : ℕ} [NeZero L] : Fintype (CyclicTiling L) :=
  by classical exact inferInstanceAs (Fintype {D : Finset (ZMod L) // IsCyclicTiling D})

/-- Rotation is a permutation of the complete finite tiling type. -/
def rotateTilingEquiv {L : ℕ} (j : ZMod L) : CyclicTiling L ≃ CyclicTiling L where
  toFun D := ⟨rotateTilings j D.1, D.2.rotate j⟩
  invFun D := ⟨rotateTilings (-j) D.1, D.2.rotate (-j)⟩
  left_inv D := by apply Subtype.ext; simp
  right_inv D := by apply Subtype.ext; simp

/-- Reflection is an involutive permutation of the complete finite tiling type. -/
def reflectTilingEquiv {L : ℕ} : CyclicTiling L ≃ CyclicTiling L where
  toFun D := ⟨reflectTilings D.1, D.2.reflect⟩
  invFun D := ⟨reflectTilings D.1, D.2.reflect⟩
  left_inv D := by apply Subtype.ext; simp
  right_inv D := by apply Subtype.ext; simp

/-- Tilings with a specified number of dominoes, for uniform weight comparison. -/
def CyclicTilingCard (L d : ℕ) := {D : Finset (ZMod L) // IsCyclicTiling D ∧ D.card = d}

instance {L : ℕ} [NeZero L] (d : ℕ) : Fintype (CyclicTilingCard L d) :=
  by classical exact inferInstanceAs (Fintype {D : Finset (ZMod L) // IsCyclicTiling D ∧ D.card = d})

/-- Every fixed rotation permutes the tilings with `d` dominoes. -/
def rotateTilingCardEquiv {L d : ℕ} (j : ZMod L) :
    CyclicTilingCard L d ≃ CyclicTilingCard L d where
  toFun D := ⟨rotateTilings j D.1, D.2.1.rotate j, by simpa using D.2.2⟩
  invFun D := ⟨rotateTilings (-j) D.1, D.2.1.rotate (-j), by simpa using D.2.2⟩
  left_inv D := by apply Subtype.ext; simp
  right_inv D := by apply Subtype.ext; simp

/-- Natural-number domino indices on a line segment of length `n`. -/
def IsLineDominoSet (n : ℕ) (D : Finset ℕ) : Prop :=
  (∀ i ∈ D, 0 < i ∧ i < n) ∧ ∀ i ∈ D, i + 1 ∉ D

/-- Embed bounded line indices in the corresponding cycle. -/
def lineToCycle (L : ℕ) (D : Finset ℕ) : Finset (ZMod L) :=
  D.image (Nat.cast : ℕ → ZMod L)

/-- Cut a cycle at zero, taking the canonical representatives of its dominoes. -/
def cycleToLine {L : ℕ} (D : Finset (ZMod L)) : Finset ℕ :=
  D.image ZMod.val

@[simp] theorem lineToCycle_cycleToLine {L : ℕ} [NeZero L]
    (D : Finset (ZMod L)) : lineToCycle L (cycleToLine D) = D := by
  simp [lineToCycle, cycleToLine, Finset.image_image]

/-- The representative map loses no bounded line index. -/
theorem IsLineDominoSet.cycleToLine_lineToCycle {L : ℕ} {D : Finset ℕ}
    (hD : IsLineDominoSet L D) : cycleToLine (lineToCycle L D) = D := by
  apply Finset.ext
  intro n
  simp only [cycleToLine, lineToCycle, Finset.mem_image]
  constructor
  · rintro ⟨r, ⟨m, hm, rfl⟩, rfl⟩
    simpa [ZMod.val_natCast_of_lt (hD.1 m hm).2] using hm
  · intro hn
    exact ⟨(n : ZMod L), ⟨n, hn, rfl⟩,
      ZMod.val_natCast_of_lt (hD.1 n hn).2⟩

/-- Legal line dominoes stay disjoint after identifying the endpoints of the line. -/
theorem IsLineDominoSet.isCyclicTiling {L : ℕ} {D : Finset ℕ}
    (hD : IsLineDominoSet L D) : IsCyclicTiling (lineToCycle L D) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b, hb, hbn⟩ := Finset.mem_image.mp hb
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
  have hmp : 0 < m := (hD.1 m hm).1
  have hml : m < L := (hD.1 m hm).2
  have hnl : n < L := (hD.1 n hn).2
  have hmcast : ((m - 1 : ℕ) : ZMod L) = (m : ZMod L) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hval := congrArg ZMod.val hbn
  rw [← hmcast, ZMod.val_natCast_of_lt (by omega : m - 1 < L),
    ZMod.val_natCast_of_lt hnl] at hval
  have : n + 1 = m := by omega
  exact hD.2 n hn (this ▸ hm)

/-- The wraparound domino is absent from an embedded line tiling. -/
theorem IsLineDominoSet.zero_not_mem {L : ℕ} {D : Finset ℕ}
    (hD : IsLineDominoSet L D) : (0 : ZMod L) ∉ lineToCycle L D := by
  intro hz
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hz
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (hD.1 n hn).2, ZMod.val_zero] at hv
  exact (Nat.ne_of_gt (hD.1 n hn).1) hv

/-- Cutting at a site with no wraparound domino gives a legal line tiling. -/
theorem IsCyclicTiling.isLineDominoSet {L : ℕ} [NeZero L]
    {D : Finset (ZMod L)} (hD : IsCyclicTiling D) (hz : 0 ∉ D) :
    IsLineDominoSet L (cycleToLine D) := by
  constructor
  · intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    refine ⟨?_, a.val_lt⟩
    by_contra h
    have he : a.val = 0 := by omega
    have : a = 0 := by
      rw [← ZMod.natCast_zmod_val a, he, Nat.cast_zero]
    exact hz (this ▸ ha)
  · intro i hi hip
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hip
    have hc := congrArg (Nat.cast : ℕ → ZMod L) hba
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at hc
    apply hD.ne_predecessor ha hb
    rw [hc]
    simp

/-- The exact cut-and-glue bijection; no prime-length or orbit-size assumption. -/
def noWrapLineEquiv (L : ℕ) [NeZero L] :
    {D : Finset (ZMod L) // IsCyclicTiling D ∧ 0 ∉ D} ≃
    {D : Finset ℕ // IsLineDominoSet L D} where
  toFun D := ⟨cycleToLine D.1, D.2.1.isLineDominoSet D.2.2⟩
  invFun D := ⟨lineToCycle L D.1, D.2.isCyclicTiling, D.2.zero_not_mem⟩
  left_inv D := by apply Subtype.ext; exact lineToCycle_cycleToLine D.1
  right_inv D := by apply Subtype.ext; exact D.2.cycleToLine_lineToCycle

/-- The canonical representative map is injective on a nonzero cycle. -/
theorem cycleToLine_card {L : ℕ} [NeZero L] (D : Finset (ZMod L)) :
    (cycleToLine D).card = D.card := by
  apply Finset.card_image_of_injective
  intro a b h
  have hc := congrArg (Nat.cast : ℕ → ZMod L) h
  simpa only [ZMod.natCast_zmod_val] using hc

/-- Gluing a bounded line tiling retains the number of dominoes. -/
theorem IsLineDominoSet.lineToCycle_card {L : ℕ} [NeZero L] {D : Finset ℕ}
    (hD : IsLineDominoSet L D) : (lineToCycle L D).card = D.card := by
  rw [← cycleToLine_card (lineToCycle L D), hD.cycleToLine_lineToCycle]

@[simp] theorem mem_rotateTilings {L : ℕ} (D : Finset (ZMod L)) (j a : ZMod L) :
    a ∈ rotateTilings j D ↔ a - j ∈ D := by
  simp only [rotateTilings, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa using hn
  · intro ha
    exact ⟨a - j, ha, sub_add_cancel _ _⟩

@[simp] theorem mem_reflectTilings {L : ℕ} (D : Finset (ZMod L)) (a : ZMod L) :
    a ∈ reflectTilings D ↔ 1 - a ∈ D := by
  simp only [reflectTilings, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa using hn
  · intro ha
    exact ⟨1 - a, ha, by simp⟩

/-- The two possible dominoes incident to zero cannot coexist. -/
theorem IsCyclicTiling.not_zero_and_one {L : ℕ} {D : Finset (ZMod L)}
    (hD : IsCyclicTiling D) : ¬((0 : ZMod L) ∈ D ∧ (1 : ZMod L) ∈ D) := by
  rintro ⟨hz, ho⟩
  exact hD.ne_predecessor hz ho (by simp)

/-- A length-one cycle has only its single tile, with no self-loop domino. -/
theorem isCyclicTiling_one_iff (D : Finset (ZMod 1)) : IsCyclicTiling D ↔ D = ∅ := by
  constructor
  · intro hD
    have hc := hD.twice_card_le
    have : D.card = 0 := by omega
    exact Finset.card_eq_zero.mp this
  · rintro rfl
    exact isCyclicTiling_empty 1

/-- The unordered physical sites of a domino. -/
def dominoSites {L : ℕ} (n : ZMod L) : Finset (ZMod L) := {n, n - 1}

/-- For cycles of length at least three, a physical domino has a unique
index. Together with the finite-set representation, this excludes both
permutation multiplicities and duplicate encodings. -/
theorem dominoSites_injective {L : ℕ} (hL : 3 ≤ L) :
    Function.Injective (@dominoSites L) := by
  intro n m h
  have hn : n ∈ dominoSites m := by rw [← h]; simp [dominoSites]
  have hm : m ∈ dominoSites n := by rw [h]; simp [dominoSites]
  simp only [dominoSites, Finset.mem_insert, Finset.mem_singleton] at hn hm
  rcases hn with hnm | hnm
  · exact hnm
  · rcases hm with hmn | hmn
    · exact hmn.symm
    · have he : m - 1 - 1 = m := by rw [← hnm, ← hmn]
      have hh : m - 1 + (-1) = m - 1 + 1 := by simpa [sub_eq_add_neg, add_assoc] using he
      have hneg : (-1 : ZMod L) = 1 := add_left_cancel hh
      have := ZMod.neg_one_eq_one_iff.mp hneg
      omega

end

end QFixLean.QuasiChebyshev
