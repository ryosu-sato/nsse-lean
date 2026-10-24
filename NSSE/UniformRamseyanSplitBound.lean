import NSSE.RamseyanSplit

/-!
# Uniform bounds for Ramseyan splits

These propositions record the quantifier order needed by the Simon
induction.  In particular, a uniform bound is independent of both the word
and the alphabet used to present the finite control monoid.

The length-bounded statement is an unconditional baseline.  The genuine
Simon step must replace its `lengthLimit + 1` height by a bound depending
only on the finite control monoid.
-/

namespace NSSE

universe u v

structure UniformRamseyanSplitBound
    (C : ControlMonoid M) (bound : Nat) : Prop where
  split :
    ∀ {α : Type u} (letter : α → M) (word : Word α),
      Nonempty (RamseyanSplit C letter word bound)

structure ControlValueRamseyanSplitBound
    (C : ControlMonoid M) (bound : Nat) : Prop where
  split :
    ∀ word : Word M,
      Nonempty (RamseyanSplit C id word bound)

structure PaletteRamseyanSplitBound
    (C : ControlMonoid M) (palette : List M)
    (bound : Nat) : Prop where
  split :
    ∀ word : Word M,
      (∀ value ∈ word, value ∈ palette) →
      Nonempty (RamseyanSplit C id word bound)

structure LengthBoundedRamseyanSplitBound
    (C : ControlMonoid M) (lengthLimit bound : Nat) : Prop where
  split :
    ∀ {α : Type u} (letter : α → M) (word : Word α),
      word.length ≤ lengthLimit →
      Nonempty (RamseyanSplit C letter word bound)

namespace UniformRamseyanSplitBound

theorem weaken
    (bounded :
      UniformRamseyanSplitBound.{u, v} C bound)
    (larger : Nat) (hle : bound ≤ larger) :
    UniformRamseyanSplitBound.{u, v} C larger where
  split := by
    intro α letter word
    obtain ⟨split⟩ := bounded.split letter word
    exact ⟨split.weaken larger hle⟩

theorem toControlValue
    (bounded :
      UniformRamseyanSplitBound.{v, v} C bound) :
    ControlValueRamseyanSplitBound C bound where
  split := by
    intro word
    exact bounded.split id word

theorem toLengthBounded
    (bounded :
      UniformRamseyanSplitBound.{u, v} C bound)
    (lengthLimit : Nat) :
    LengthBoundedRamseyanSplitBound.{u, v}
      C lengthLimit bound where
  split := by
    intro α letter word _
    exact bounded.split letter word

end UniformRamseyanSplitBound

namespace ControlValueRamseyanSplitBound

theorem weaken
    (bounded : ControlValueRamseyanSplitBound C bound)
    (larger : Nat) (hle : bound ≤ larger) :
    ControlValueRamseyanSplitBound C larger where
  split := by
    intro word
    obtain ⟨split⟩ := bounded.split word
    exact ⟨split.weaken larger hle⟩

theorem toPalette
    {M : Type v} {C : ControlMonoid M}
    (bounded : ControlValueRamseyanSplitBound C bound)
    (palette : List M) :
    PaletteRamseyanSplitBound C palette bound where
  split := by
    intro word _
    exact bounded.split word

theorem toUniform
    (bounded : ControlValueRamseyanSplitBound C bound) :
    UniformRamseyanSplitBound.{u, v} C bound where
  split := by
    intro α letter word
    obtain ⟨split⟩ := bounded.split (word.map letter)
    exact ⟨RamseyanSplit.ofControlWord
      C letter word split⟩

end ControlValueRamseyanSplitBound

namespace PaletteRamseyanSplitBound

theorem weaken
    (bounded :
      PaletteRamseyanSplitBound C palette bound)
    (larger : Nat) (hle : bound ≤ larger) :
    PaletteRamseyanSplitBound C palette larger where
  split := by
    intro word hpalette
    obtain ⟨split⟩ := bounded.split word hpalette
    exact ⟨split.weaken larger hle⟩

theorem mono
    (bounded :
      PaletteRamseyanSplitBound C largerPalette bound)
    (hsubset :
      ∀ value, value ∈ palette → value ∈ largerPalette) :
    PaletteRamseyanSplitBound C palette bound where
  split := by
    intro word hpalette
    apply bounded.split word
    intro value hvalue
    exact hsubset value (hpalette value hvalue)

theorem empty
    (C : ControlMonoid M) :
    PaletteRamseyanSplitBound C [] 1 where
  split := by
    intro word hpalette
    have hword : word = [] := by
      cases word with
      | nil => rfl
      | cons head tail =>
          have := hpalette head (by simp)
          simp at this
    subst word
    exact ⟨RamseyanSplit.byDistinctCuts C id []⟩

theorem toControlValue
    [DecidableEq M]
    (elements : Enumeration M)
    (bounded :
      PaletteRamseyanSplitBound C
        elements.normalized.values bound) :
    ControlValueRamseyanSplitBound C bound where
  split := by
    intro word
    apply bounded.split word
    intro value _
    exact elements.normalized.complete value

theorem exists_of_palette_length_recursion
    (C : ControlMonoid M) (palette : List M)
    (step :
      ∀ current : List M,
        (∀ smaller : List M,
          smaller.length < current.length →
          ∃ bound,
            PaletteRamseyanSplitBound C smaller bound) →
        ∃ bound,
          PaletteRamseyanSplitBound C current bound) :
    ∃ bound,
      PaletteRamseyanSplitBound C palette bound := by
  have solve :
      ∀ size : Nat, ∀ current : List M,
        current.length = size →
        ∃ bound,
          PaletteRamseyanSplitBound C current bound := by
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
    {M : Type v} [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (palette : List M)
    (step :
      ∀ {N : Type v} [DecidableEq N]
        (D : ControlMonoid N) (finite : Enumeration N)
        (current : List N),
        (∀ {P : Type v} [DecidableEq P]
          (E : ControlMonoid P)
          (smallerFinite : Enumeration P),
          smallerFinite.normalized.values.length <
              finite.normalized.values.length →
          ∀ smallerPalette : List P,
            ∃ bound,
              PaletteRamseyanSplitBound
                E smallerPalette bound) →
        (∀ smallerPalette : List N,
          smallerPalette.length < current.length →
          ∃ bound,
            PaletteRamseyanSplitBound
              D smallerPalette bound) →
        ∃ bound,
          PaletteRamseyanSplitBound D current bound) :
    ∃ bound,
      PaletteRamseyanSplitBound C palette bound := by
  have solveControl :
      ∀ controlSize : Nat,
        ∀ {N : Type v} [DecidableEq N]
          (D : ControlMonoid N) (finite : Enumeration N),
          finite.normalized.values.length = controlSize →
          ∀ current : List N,
            ∃ bound,
              PaletteRamseyanSplitBound
                D current bound := by
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
                  PaletteRamseyanSplitBound
                    D active bound := by
          intro paletteSize
          induction paletteSize using Nat.strongRecOn with
          | ind paletteSize paletteIH =>
              intro active hpaletteSize
              apply step D finite active
              · intro P _ E smallerFinite hsmaller
                intro smallerPalette
                exact controlIH
                  smallerFinite.normalized.values.length
                  (by
                    simpa [hcontrolSize] using hsmaller)
                  E smallerFinite rfl smallerPalette
              · intro smallerPalette hsmaller
                apply paletteIH smallerPalette.length
                · simpa [hpaletteSize] using hsmaller
                · rfl
        exact solvePalette current.length current rfl
  exact solveControl
    elements.normalized.values.length
    C elements rfl palette

end PaletteRamseyanSplitBound

namespace LengthBoundedRamseyanSplitBound

theorem weakenHeight
    (bounded :
      LengthBoundedRamseyanSplitBound.{u, v}
        C lengthLimit bound)
    (larger : Nat) (hle : bound ≤ larger) :
    LengthBoundedRamseyanSplitBound.{u, v}
      C lengthLimit larger where
  split := by
    intro α letter word hlength
    obtain ⟨split⟩ := bounded.split letter word hlength
    exact ⟨split.weaken larger hle⟩

theorem weakenLength
    (bounded :
      LengthBoundedRamseyanSplitBound.{u, v}
        C largerLimit bound)
    (hlimit : lengthLimit ≤ largerLimit) :
    LengthBoundedRamseyanSplitBound.{u, v}
      C lengthLimit bound where
  split := by
    intro α letter word hlength
    exact bounded.split letter word
      (Nat.le_trans hlength hlimit)

theorem byDistinctCuts
    (C : ControlMonoid M) (lengthLimit : Nat) :
    LengthBoundedRamseyanSplitBound.{u, v}
      C lengthLimit (lengthLimit + 1) where
  split := by
    intro α letter word hlength
    let split :=
      RamseyanSplit.byDistinctCuts C letter word
    exact ⟨split.weaken (lengthLimit + 1)
      (Nat.add_le_add_right hlength 1)⟩

end LengthBoundedRamseyanSplitBound

end NSSE
