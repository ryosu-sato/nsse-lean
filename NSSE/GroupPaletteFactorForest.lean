import NSSE.LocalDivisorPortLift

/-!
# Uniform forests for palettes of invertible control values

If every letter value is two-sided invertible, every prefix value is
invertible.  Color a cut by the canonical finite index of its prefix
value.  Equal colors give equal prefix values, and left cancellation then
shows that the intervening interval evaluates to the unit.  This is a
Ramseyan split whose every level carries the unit idempotent.
-/

namespace NSSE

universe u v

namespace ControlMonoid

theorem hasTwoSidedInverse_one
    (C : ControlMonoid M) :
    C.HasTwoSidedInverse C.one := by
  exact ⟨⟨C.one, C.mul_one C.one⟩,
    C.one, C.one_mul C.one⟩

theorem HasTwoSidedInverse.mul
    (C : ControlMonoid M) {left right : M}
    (hleft : C.HasTwoSidedInverse left)
    (hright : C.HasTwoSidedInverse right) :
    C.HasTwoSidedInverse (C.mul left right) := by
  obtain ⟨⟨leftRight, hleftRight⟩,
    leftLeft, hleftLeft⟩ := hleft
  obtain ⟨⟨rightRight, hrightRight⟩,
    rightLeft, hrightLeft⟩ := hright
  constructor
  · refine ⟨C.mul rightRight leftRight, ?_⟩
    calc
      C.mul (C.mul left right)
          (C.mul rightRight leftRight) =
        C.mul left
          (C.mul (C.mul right rightRight)
            leftRight) := by
              simp only [C.mul_assoc]
      _ = C.mul left (C.mul C.one leftRight) := by
            rw [hrightRight]
      _ = C.one := by
            rw [C.one_mul, hleftRight]
  · refine ⟨C.mul rightLeft leftLeft, ?_⟩
    calc
      C.mul (C.mul rightLeft leftLeft)
          (C.mul left right) =
        C.mul rightLeft
          (C.mul (C.mul leftLeft left)
            right) := by
              simp only [C.mul_assoc]
      _ = C.mul rightLeft (C.mul C.one right) := by
            rw [hleftLeft]
      _ = C.one := by
            rw [C.one_mul, hrightLeft]

theorem eval_hasTwoSidedInverse
    (C : ControlMonoid M) (letter : α → M) :
    ∀ word : Word α,
      (∀ symbol ∈ word,
        C.HasTwoSidedInverse (letter symbol)) →
      C.HasTwoSidedInverse (C.eval letter word) := by
  intro word hall
  induction word with
  | nil =>
      exact C.hasTwoSidedInverse_one
  | cons head tail ih =>
      change C.HasTwoSidedInverse
        (C.mul (letter head) (C.eval letter tail))
      exact ControlMonoid.HasTwoSidedInverse.mul C
        (hall head (by simp))
        (ih (by
          intro symbol hsymbol
          exact hall symbol (by simp [hsymbol])))

theorem eq_one_of_mul_eq_self_of_invertible
    (C : ControlMonoid M) {prefixValue intervalValue : M}
    (hinvertible : C.HasTwoSidedInverse prefixValue)
    (heq : C.mul prefixValue intervalValue = prefixValue) :
    intervalValue = C.one := by
  obtain ⟨_, leftInverse, hleftInverse⟩ :=
    hinvertible
  have hmul :=
    congrArg (C.mul leftInverse) heq
  simpa only [← C.mul_assoc, hleftInverse,
    C.one_mul] using hmul

end ControlMonoid

noncomputable def groupPaletteRamseyanSplit
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M)
    (hinvertible :
      ∀ value ∈ palette,
        C.HasTwoSidedInverse value)
    (word : Word M)
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    RamseyanSplit C id word
      elements.normalized.values.length where
  rank := fun cut =>
    elements.canonicalIndex
      (C.eval id (word.take cut.1))
  idempotentAt := fun _ => C.one
  idempotent := by
    intro _
    exact C.mul_one C.one
  neighbor_control := by
    intro left right hneighbors
    have hpref :
        C.eval id (word.take left.1) =
          C.eval id (word.take right.1) := by
      have hindex :=
        congrArg elements.valueAt hneighbors.2.1
      simpa using hindex
    have htake :=
      ControlMonoid.take_append_middleFactor
        word (Nat.le_of_lt hneighbors.1)
    have heval :=
      congrArg (C.eval id) htake
    rw [C.eval_append] at heval
    have hfix :
        C.mul (C.eval id (word.take left.1))
            (C.eval id
              (WordCut.interval word left right)) =
          C.eval id (word.take left.1) := by
      exact heval.trans hpref.symm
    apply C.eq_one_of_mul_eq_self_of_invertible
      (intervalValue :=
        C.eval id (WordCut.interval word left right))
      ?_ hfix
    apply C.eval_hasTwoSidedInverse id
    intro value hvalue
    apply hinvertible value
    apply hpalette value
    exact List.mem_of_mem_take hvalue

theorem groupPaletteFactorForestBound
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M)
    (hinvertible :
      ∀ value ∈ palette,
        C.HasTwoSidedInverse value) :
    PaletteFactorForestBound C palette
      (5 * elements.normalized.values.length) where
  forest := by
    intro word hword hpalette
    exact ⟨(groupPaletteRamseyanSplit
      C elements palette hinvertible word hpalette
      ).toFactorForest
        elements.normalized.values.length hword⟩

theorem exists_paletteFactorForestBound
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M) :
    ∃ bound,
      PaletteFactorForestBound C palette bound := by
  apply PaletteFactorForestBound.exists_of_control_palette_recursion
    C elements palette
  intro N _ D finite current
    smallerControl smallerPalette
  classical
  by_cases hall :
      ∀ value ∈ current,
        D.HasTwoSidedInverse value
  · exact ⟨5 * finite.normalized.values.length,
      groupPaletteFactorForestBound
        D finite current hall⟩
  · have hexists :
        ∃ value, value ∈ current ∧
          ¬ D.HasTwoSidedInverse value := by
      apply Classical.byContradiction
      intro hnone
      apply hall
      intro value hvalue
      exact Classical.byContradiction
        (fun hnonunit =>
          hnone ⟨value, hvalue, hnonunit⟩)
    obtain ⟨pivot, hpivot, hnonunit⟩ := hexists
    exact
      NonunitPivotSimonData.exists_palette_bound_of_nonunit
        D finite current pivot hpivot hnonunit
        smallerControl smallerPalette

theorem exists_uniformFactorForestBound
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M) :
    ∃ bound,
      UniformFactorForestBound.{u, v} C bound := by
  obtain ⟨bound, paletteBound⟩ :=
    exists_paletteFactorForestBound
      C elements elements.normalized.values
  exact ⟨bound,
    (paletteBound.toControlValue elements).toUniform⟩

end NSSE
