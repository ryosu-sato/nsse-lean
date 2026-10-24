import NSSE.MinimalZeroPrefixForest

/-!
# The complete local forest step for a zero-valued word

This composes the greedy zero-factor decomposition with the proper
right-stabilizer forest for the first zero prefix.
-/

namespace NSSE

universe u v

namespace ControlMonoid

noncomputable def zeroValuedWordForestStep
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (zero : M)
    (hzeroOne : zero ≠ C.one)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (word : Word α) (hword : word ≠ [])
    (hcontrol : C.eval letter word = zero)
    (innerBound outerBound : Nat)
    (properUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound
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
  let first :=
    C.firstZeroPrefix letter zero hzeroOne
      word hword hcontrol
  let decomposition :=
    Classical.choice
      (C.zeroFactorBlockDecomposition_nonempty
        letter zero hzeroOne word hword hcontrol)
  let prefixBound :=
    max (3 * elements.normalized.values.length)
      (innerBound + outerBound + 2)
  have hinnerPrefix : innerBound ≤ prefixBound := by
    dsimp [prefixBound]
    exact Nat.le_trans
      (by omega : innerBound ≤ innerBound + outerBound + 2)
      (Nat.le_max_right _ _)
  have prefixForest :
      FactorTree.HeightBoundedForest
        C letter (word.take first.cut) prefixBound := by
    apply first.forest elements hleft
      innerBound outerBound properUniform
    intro subword hsubword hsubwordNe
    apply recursive subword
    · exact Nat.lt_of_lt_of_le hsubword
        (by
          simp only [List.length_take]
          exact Nat.min_le_right _ _)
    · exact hsubwordNe
  have strictForest :
      ∀ block ∈ decomposition.blocks,
        block.length < word.length →
        FactorTree.HeightBoundedForest
          C letter block prefixBound := by
    intro block hblock hlength
    exact (recursive block hlength
      (decomposition.block_ne block hblock)).weaken
        prefixBound hinnerPrefix
  have suffixForest :
      word.drop first.cut ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop first.cut) prefixBound := by
    intro hsuffix
    have hsuffixLength :
        (word.drop first.cut).length < word.length := by
      have hwordPositive :
          0 < word.length :=
        List.length_pos_iff.mpr hword
      simp only [List.length_drop]
      exact Nat.sub_lt hwordPositive first.positive
    exact (recursive (word.drop first.cut)
      hsuffixLength hsuffix).weaken prefixBound hinnerPrefix
  exact decomposition.forestOfFirstZeroPrefix
    first hright hleft strictForest prefixForest suffixForest

end ControlMonoid

end NSSE
