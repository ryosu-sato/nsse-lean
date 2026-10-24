import NSSE.PivotGapDecomposition
import NSSE.FiniteAlphabetSimonReduction

/-!
# Uniform forest bounds restricted to a finite control palette

The local-divisor proof needs a second induction parameter besides the monoid:
the set of control values allowed as letters.  Splitting at a pivot removes
that pivot from every gap, while products of the delimited blocks are handled
by the smaller local divisor.
-/

namespace NSSE

universe v

structure PaletteFactorForestBound
    (C : ControlMonoid M) (palette : List M) (bound : Nat) : Prop where
  forest :
    ∀ word : Word M, word ≠ [] →
      (∀ value ∈ word, value ∈ palette) →
      Nonempty
        (FactorTree.HeightBoundedForest C id word bound)

namespace PaletteFactorForestBound

theorem weaken
    (bounded : PaletteFactorForestBound C palette bound)
    (larger : Nat) (hle : bound ≤ larger) :
    PaletteFactorForestBound C palette larger where
  forest := by
    intro word hword hpalette
    obtain ⟨forest⟩ := bounded.forest word hword hpalette
    exact ⟨forest.weaken larger hle⟩

theorem empty
    (C : ControlMonoid M) :
    PaletteFactorForestBound C [] 0 where
  forest := by
    intro word hword hpalette
    cases word with
    | nil => exact False.elim (hword rfl)
    | cons head tail =>
        have := hpalette head (by simp)
        simp at this

theorem toControlValue
    [DecidableEq M]
    (elements : Enumeration M)
    (bounded :
      PaletteFactorForestBound C
        elements.normalized.values bound) :
    ControlValueFactorForestBound C bound where
  forest := by
    intro word hword
    apply bounded.forest word hword
    intro value hvalue
    exact elements.normalized.complete value

theorem mem_erase_of_mem_of_ne
    [DecidableEq M]
    {pivot value : M} {palette : List M}
    (hvalue : value ∈ palette) (hne : value ≠ pivot) :
    value ∈ palette.erase pivot := by
  exact (List.mem_erase_of_ne hne).2 hvalue

theorem erase_length_lt
    [DecidableEq M]
    {pivot : M} {palette : List M}
    (hpivot : pivot ∈ palette) :
    (palette.erase pivot).length < palette.length := by
  rw [List.length_erase_of_mem hpivot]
  have hpositive : 0 < palette.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem hpivot)
  omega

theorem exists_of_palette_length_recursion
    (C : ControlMonoid M) (palette : List M)
    (step :
      ∀ current : List M,
        (∀ smaller : List M,
          smaller.length < current.length →
          ∃ bound,
            PaletteFactorForestBound C smaller bound) →
        ∃ bound,
          PaletteFactorForestBound C current bound) :
    ∃ bound,
      PaletteFactorForestBound C palette bound := by
  have solve :
      ∀ size : Nat, ∀ current : List M,
        current.length = size →
        ∃ bound,
          PaletteFactorForestBound C current bound := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro current hsize
        apply step current
        intro smaller hsmaller
        apply ih smaller.length
        · simpa [hsize] using hsmaller
        · rfl
  exact solve palette.length palette rfl

theorem exists_of_control_palette_recursion
    {M : Type v}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M)
    (step :
      ∀ {N : Type v} [DecidableEq N]
        (D : ControlMonoid N) (finite : Enumeration N)
        (current : List N),
        (∀ {P : Type v} [DecidableEq P]
          (E : ControlMonoid P) (smallerFinite : Enumeration P),
          smallerFinite.normalized.values.length <
              finite.normalized.values.length →
          ∀ smallerPalette : List P,
            ∃ bound,
              PaletteFactorForestBound
                E smallerPalette bound) →
        (∀ smallerPalette : List N,
          smallerPalette.length < current.length →
          ∃ bound,
            PaletteFactorForestBound
              D smallerPalette bound) →
        ∃ bound,
          PaletteFactorForestBound D current bound) :
    ∃ bound,
      PaletteFactorForestBound C palette bound := by
  have solveControl :
      ∀ controlSize : Nat,
        ∀ {N : Type v} [DecidableEq N]
          (D : ControlMonoid N) (finite : Enumeration N),
          finite.normalized.values.length = controlSize →
          ∀ current : List N,
            ∃ bound,
              PaletteFactorForestBound D current bound := by
    intro controlSize
    induction controlSize using Nat.strongRecOn with
    | ind controlSize controlIH =>
        intro N _ D finite hcontrolSize
        intro current
        have solvePalette :
            ∀ paletteSize : Nat,
              ∀ active : List N,
                active.length = paletteSize →
                ∃ bound,
                  PaletteFactorForestBound D active bound := by
          intro paletteSize
          induction paletteSize using Nat.strongRecOn with
          | ind paletteSize paletteIH =>
              intro active hpaletteSize
              apply step D finite active
              · intro P _ E smallerFinite hsmaller
                intro smallerPalette
                exact controlIH
                  smallerFinite.normalized.values.length
                  (by simpa [hcontrolSize] using hsmaller)
                  E smallerFinite rfl smallerPalette
              · intro smallerPalette hsmaller
                apply paletteIH smallerPalette.length
                · simpa [hpaletteSize] using hsmaller
                · rfl
        exact solvePalette current.length current rfl
  exact solveControl elements.normalized.values.length
    C elements rfl palette

theorem gap_mem_erased_palette
    [DecidableEq M]
    {pivot : M} {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    {palette : List M}
    (hpalette :
      ∀ value ∈ word, value ∈ palette) :
    ∀ gap ∈ gaps, ∀ value ∈ gap,
      value ∈ palette.erase pivot := by
  intro gap hgap value hvalue
  apply mem_erase_of_mem_of_ne
  · apply hpalette value
    rw [← decomposition.join_eq]
    exact mem_joinPivotGaps_of_mem_gap
      pivot hgap hvalue
  · intro heq
    subst value
    exact decomposition.gaps_avoid gap hgap hvalue

theorem nonempty_gap_forests
    [DecidableEq M]
    {pivot : M} {word : Word M} {gaps : List (Word M)}
    (decomposition :
      PivotGapDecomposition pivot word gaps)
    {palette : List M}
    (hpalette :
      ∀ value ∈ word, value ∈ palette)
    (gapBound :
      PaletteFactorForestBound C (palette.erase pivot) bound) :
    ∀ gap ∈ gaps, gap ≠ [] →
      Nonempty
        (FactorTree.HeightBoundedForest C id gap bound) := by
  intro gap hgap hnonempty
  apply gapBound.forest gap hnonempty
  exact gap_mem_erased_palette decomposition
    hpalette gap hgap

end PaletteFactorForestBound

end NSSE
