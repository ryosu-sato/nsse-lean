import NSSE.UniformFactorForestBound
import NSSE.BilateralSimonStep

/-!
# Whole-word forest for the proper-right-stabilizer branch

Four equal prefix controls give three consecutive blocks in one proper
right stabilizer.  Graft its uniform forest and surround it by the two
strictly shorter exterior pieces.
-/

namespace NSSE

universe u v

namespace ControlMonoid.FourPrefixControlCuts

noncomputable def properRightWordForest
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M} {word : Word α}
    (cuts : C.FourPrefixControlCuts letter word)
    (innerBound outerBound : Nat)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.rightStabilizer cuts.anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest C letter word
      (innerBound + outerBound + 2) := by
  let indices := [cuts.i₀, cuts.i₁, cuts.i₂, cuts.i₃]
  have h01 := cuts.lt₀₁
  have h12 := cuts.lt₁₂
  have h23 := cuts.lt₂₃
  have hi3 := cuts.i₃_le
  have hindices : 2 ≤ indices.length := by
    simp [indices]
  have hordered : indices.Pairwise (· < ·) := by
    simp [indices]
    omega
  have hbounded :
      ∀ index ∈ indices, index ≤ word.length := by
    intro index hindex
    simp [indices] at hindex
    rcases hindex with rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · exact cuts.i₃_le
  have hcontrol :
      ∀ index ∈ indices,
        C.eval letter (word.take index) = cuts.anchor := by
    intro index hindex
    simp [indices] at hindex
    rcases hindex with rfl | rfl | rfl | rfl
    · rfl
    · exact cuts.equal₀₁.symm
    · exact cuts.equal₀₂.symm
    · exact cuts.equal₀₃.symm
  have replacementNonempty :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        Nonempty
          (FactorTree.HeightBoundedForest
            C letter block innerBound) := by
    intro block hblock
    simp [indices, ControlMonoid.blocksBetweenCuts] at hblock
    rcases hblock with rfl | rfl | rfl
    · exact ⟨recursive cuts.block₀₁
        cuts.block₀₁_length_lt cuts.block₀₁_ne_nil⟩
    · exact ⟨recursive cuts.block₁₂
        cuts.block₁₂_length_lt cuts.block₁₂_ne_nil⟩
    · exact ⟨recursive cuts.block₂₃
        cuts.block₂₃_length_lt cuts.block₂₃_ne_nil⟩
  let replacement :
      ∀ block ∈ ControlMonoid.blocksBetweenCuts word indices,
        FactorTree.HeightBoundedForest
          C letter block innerBound :=
    fun block hblock =>
      Classical.choice (replacementNonempty block hblock)
  let middle :=
    Classical.choice
      (UniformFactorForestBound.graft_equal_prefix_blocks
        letter word cuts.anchor indices
        hindices hordered hbounded hcontrol
        uniformOuter replacement)
  have hwhole :
      word.take cuts.i₀ ++
          (ControlMonoid.blocksBetweenCuts
            word indices).flatten ++
          word.drop cuts.i₃ =
        word := by
    simpa [indices, ControlMonoid.blocksBetweenCuts,
      List.append_assoc] using cuts.three_block_word_eq
  exact FactorTree.HeightBoundedForest.surround
    middle
    (fun hnonempty =>
      (recursive (word.take cuts.i₀)
        cuts.before_length_lt hnonempty).weaken
          (innerBound + outerBound) (by omega))
    (fun hnonempty =>
      (recursive (word.drop cuts.i₃)
        cuts.after_length_lt hnonempty).weaken
          (innerBound + outerBound) (by omega))
    hwhole

end ControlMonoid.FourPrefixControlCuts

end NSSE
