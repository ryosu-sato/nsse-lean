import NSSE.ZeroValuedWordForestStep
import NSSE.NonzeroValuedWordForestStep

/-!
# The combined local forest step for a two-sided zero

The total word control is either the fixed zero or is different from it.
The two previously constructed branches therefore give one forest step for
every nonempty word, with a common height expression.
-/

namespace NSSE

universe u v

namespace ControlMonoid

noncomputable def twoSidedZeroWordForestStep
    {M : Type v} {α : Type u}
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    (zero : M) (hzeroOne : zero ≠ C.one)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (word : Word α) (hword : word ≠ [])
    (innerBound outerBound : Nat)
    (properUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest C letter word
      (max (3 * elements.normalized.values.length)
        (innerBound + outerBound + 2) + 2) := by
  by_cases hcontrol : C.eval letter word = zero
  · exact C.zeroValuedWordForestStep
      elements letter zero hzeroOne hright hleft
      word hword hcontrol innerBound outerBound
      properUniform recursive
  · exact
      (C.nonzeroValuedWordForestStep
        elements letter zero hright hleft
        word hword hcontrol innerBound outerBound
        properUniform recursive).weaken
          (max (3 * elements.normalized.values.length)
            (innerBound + outerBound + 2) + 2)
          (by omega)

theorem twoSidedZeroWordForestStep_search_success
    {M : Type v} {α : Type u}
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    (zero : M) (hzeroOne : zero ≠ C.one)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (word : Word α) (hword : word ≠ [])
    (innerBound outerBound : Nat)
    (properUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
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
  by_cases hcontrol : C.eval letter word = zero
  · let forest :=
      C.zeroValuedWordForestStep
        elements letter zero hzeroOne hright hleft
        word hword hcontrol innerBound outerBound
        properUniform recursive
    exact ⟨forest.tree, forest.isForest,
      forest.yield_eq, forest.height_le⟩
  · let smaller :=
      C.nonzeroValuedWordForestStep
        elements letter zero hright hleft
        word hword hcontrol innerBound outerBound
        properUniform recursive
    let forest :=
      smaller.weaken
        (max (3 * elements.normalized.values.length)
          (innerBound + outerBound + 2) + 2)
        (by omega)
    exact ⟨forest.tree, forest.isForest,
      forest.yield_eq, forest.height_le⟩

noncomputable def BilateralSimonStep.absorbingBoth_wordForest
    {M : Type v} {α : Type u}
    [DecidableEq M]
    {C : ControlMonoid M} {elements : Enumeration M}
    {letter : α → M} {word : Word α}
    (step : BilateralSimonStep C elements letter word)
    (hlength : 1 < elements.normalized.values.length)
    (hresidual :
      ∃ prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq,
        step = .absorbingBoth
          prefixCuts prefixIdempotent rightAbsorbing
          suffixAnchor suffixIndices suffixLength suffixOrdered
          suffixBounded suffixControl suffixIdempotent leftAbsorbing
          anchorsEq)
    (hword : word ≠ [])
    (innerBound outerBound : Nat)
    (properUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound.{u, v}
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest C letter word
      (max (3 * elements.normalized.values.length)
        (innerBound + outerBound + 2) + 2) := by
  have hzero :=
    step.absorbingBoth_nontrivial_zero_control
      hlength hresidual
  let zero := Classical.choose hzero
  have hzeroSpec := Classical.choose_spec hzero
  exact C.twoSidedZeroWordForestStep
    elements letter zero hzeroSpec.1
    hzeroSpec.2.2.2.1 hzeroSpec.2.2.2.2
    word hword innerBound outerBound properUniform recursive

end ControlMonoid

end NSSE
