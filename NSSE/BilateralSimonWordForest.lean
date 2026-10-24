import NSSE.ProperRightStabilizerWordForest
import NSSE.ProperLeftStabilizerWordForest
import NSSE.TwoSidedZeroWordForestStep

/-!
# Complete local forest handler for the bilateral Simon step

All four constructors of `BilateralSimonStep` now produce a whole-word
factor forest at one common height.
-/

namespace NSSE

universe u v

namespace ControlMonoid.BilateralSimonStep

noncomputable def wordForest
    {M : Type v} {α : Type u}
    [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {letter : α → M} {word : Word α}
    (step : BilateralSimonStep C elements letter word)
    (hword : word ≠ [])
    (hlength : 1 < elements.normalized.values.length)
    (innerBound outerBound : Nat)
    (uniformRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (uniformLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest C letter word
      (max (3 * elements.normalized.values.length)
        (innerBound + outerBound + 2) + 2) := by
  cases step with
  | short hshort =>
      exact
        (C.shortSimonStepForest
          elements letter word hword hshort).weaken _ (by omega)
  | properRight cuts hproper _ =>
      exact
        (cuts.properRightWordForest
          innerBound outerBound
          (uniformRight cuts.anchor hproper)
          recursive).weaken _ (by omega)
  | properLeft anchor indices hindices hordered hbounded
      hcontrol hproper _ =>
      let cuts : C.FourSuffixControlCuts letter word :=
        {
          anchor := anchor
          indices := indices
          length_eq := hindices
          ordered := hordered
          bounded := hbounded
          equal_control := hcontrol
        }
      exact
        (cuts.properLeftWordForest
          innerBound outerBound
          (uniformLeft anchor hproper)
          recursive).weaken _ (by omega)
  | absorbingBoth prefixCuts prefixIdempotent rightAbsorbing
      suffixAnchor suffixIndices suffixLength suffixOrdered
      suffixBounded suffixControl suffixIdempotent leftAbsorbing
      anchorsEq =>
      let residual :
          BilateralSimonStep C elements letter word :=
        .absorbingBoth
          prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq
      exact residual.absorbingBoth_wordForest
        hlength
        ⟨prefixCuts, prefixIdempotent, rightAbsorbing,
          suffixAnchor, suffixIndices, suffixLength, suffixOrdered,
          suffixBounded, suffixControl, suffixIdempotent,
          leftAbsorbing, anchorsEq, rfl⟩
        hword innerBound outerBound uniformRight recursive

noncomputable def finiteWordForest
    {M : Type v} {α : Type u}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hword : word ≠ [])
    (hlength : 1 < elements.normalized.values.length)
    (innerBound outerBound : Nat)
    (uniformRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (uniformLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest C letter word
      (max (3 * elements.normalized.values.length)
        (innerBound + outerBound + 2) + 2) :=
  (C.finiteBilateralSimonStep elements letter word).wordForest
    hword hlength innerBound outerBound
    uniformRight uniformLeft recursive

theorem finiteWordForest_search_success
    {M : Type v} {α : Type u}
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hword : word ≠ [])
    (hlength : 1 < elements.normalized.values.length)
    (innerBound outerBound : Nat)
    (uniformRight :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (uniformLeft :
      ∀ anchor : M,
        (C.leftStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.leftStabilizer anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    (findHeightBoundedForest?
      alphabet C letter word
      (max (3 * elements.normalized.values.length)
        (innerBound + outerBound + 2) + 2)).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  let forest :=
    finiteWordForest C
      elements letter word hword hlength
      innerBound outerBound uniformRight uniformLeft recursive
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

end ControlMonoid.BilateralSimonStep

end NSSE
