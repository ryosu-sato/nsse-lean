import NSSE.ZeroFactorBlockDecomposition
import NSSE.UniformFactorForestBound

/-!
# A uniform forest step for the first zero prefix

The first zero prefix is either short, or four repeated prefix controls
inside it have a proper right stabilizer.  In the latter case the uniform
submonoid bound and recursive forests for the strictly shorter pieces
assemble a forest for the whole prefix.
-/

namespace NSSE

universe u v

namespace ControlMonoid.FirstZeroPrefix

noncomputable def forest
    [DecidableEq M]
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α}
    (elements : Enumeration M)
    (first : C.FirstZeroPrefix letter zero word)
    (hzeroRight : ∀ value : M, C.mul value zero = zero)
    (innerBound outerBound : Nat)
    (properUniform :
      ∀ anchor : M,
        (C.rightStabilizer anchor).Proper →
        UniformFactorForestBound
          (C.rightStabilizer anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < (word.take first.cut).length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest
      C letter (word.take first.cut)
      (max (3 * elements.normalized.values.length)
        (innerBound + outerBound + 2)) := by
  let prefixWord := word.take first.cut
  let target :=
    max (3 * elements.normalized.values.length)
      (innerBound + outerBound + 2)
  by_cases hshort :
      prefixWord.length + 1 ≤
        3 * elements.normalized.values.length
  · let shortForest :=
      C.shortSimonStepForest elements letter prefixWord
        first.prefix_ne_nil hshort
    exact shortForest.weaken target
      (Nat.le_max_left _ _)
  · have hlong :
        3 * elements.normalized.values.length <
          prefixWord.length + 1 := by
      omega
    let cuts :=
      Classical.choice
        (C.exists_fourPrefixControlCuts
          elements letter prefixWord hlong)
    have h01 := cuts.lt₀₁
    have h12 := cuts.lt₁₂
    have h23 := cuts.lt₂₃
    have hi3 := cuts.i₃_le
    have hproper :
        (C.rightStabilizer cuts.anchor).Proper :=
      first.proper_rightStabilizer_of_fourCuts
        hzeroRight cuts
    let indices := [cuts.i₀, cuts.i₁, cuts.i₂, cuts.i₃]
    have hindices : 2 ≤ indices.length := by
      simp [indices]
    have hordered : indices.Pairwise (· < ·) := by
      simp [indices]
      omega
    have hbounded :
        ∀ index ∈ indices, index ≤ prefixWord.length := by
      intro index hindex
      simp [indices] at hindex
      rcases hindex with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · exact cuts.i₃_le
    have hcontrol :
        ∀ index ∈ indices,
          C.eval letter (prefixWord.take index) = cuts.anchor := by
      intro index hindex
      simp [indices] at hindex
      rcases hindex with rfl | rfl | rfl | rfl
      · rfl
      · exact cuts.equal₀₁.symm
      · exact cuts.equal₀₂.symm
      · exact cuts.equal₀₃.symm
    have replacementNonempty :
        ∀ block ∈ ControlMonoid.blocksBetweenCuts prefixWord indices,
          Nonempty
            (FactorTree.HeightBoundedForest
              C letter block innerBound) := by
      intro block hblock
      simp [indices, blocksBetweenCuts] at hblock
      rcases hblock with rfl | rfl | rfl
      · exact ⟨recursive cuts.block₀₁
          cuts.block₀₁_length_lt cuts.block₀₁_ne_nil⟩
      · exact ⟨recursive cuts.block₁₂
          cuts.block₁₂_length_lt cuts.block₁₂_ne_nil⟩
      · exact ⟨recursive cuts.block₂₃
          cuts.block₂₃_length_lt cuts.block₂₃_ne_nil⟩
    let replacement :
        ∀ block ∈ ControlMonoid.blocksBetweenCuts prefixWord indices,
          FactorTree.HeightBoundedForest
            C letter block innerBound :=
      fun block hblock =>
        Classical.choice (replacementNonempty block hblock)
    let middle :=
      Classical.choice
        (UniformFactorForestBound.graft_equal_prefix_blocks
          letter prefixWord cuts.anchor indices
          hindices hordered hbounded hcontrol
          (properUniform cuts.anchor hproper)
          replacement)
    have hwhole :
        prefixWord.take cuts.i₀ ++
            (ControlMonoid.blocksBetweenCuts
              prefixWord indices).flatten ++
            prefixWord.drop cuts.i₃ =
          prefixWord := by
      simpa [indices, blocksBetweenCuts,
        List.append_assoc] using cuts.three_block_word_eq
    let assembled :=
      FactorTree.HeightBoundedForest.surround
        middle
        (fun hnonempty =>
          (recursive (prefixWord.take cuts.i₀)
            cuts.before_length_lt hnonempty).weaken
              (innerBound + outerBound) (by omega))
        (fun hnonempty =>
          (recursive (prefixWord.drop cuts.i₃)
            cuts.after_length_lt hnonempty).weaken
              (innerBound + outerBound) (by omega))
        hwhole
    exact assembled.weaken target
      (Nat.le_max_right _ _)

end ControlMonoid.FirstZeroPrefix

end NSSE
