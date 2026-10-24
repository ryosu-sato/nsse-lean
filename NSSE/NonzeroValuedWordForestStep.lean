import NSSE.UniformFactorForestBound
import NSSE.BilateralSimonStep

/-!
# The local forest step for a nonzero-valued word

Relative to a fixed two-sided zero, a long word whose total control is not
zero has a repeated-prefix anchor distinct from zero.  Its right stabilizer
is therefore proper, so the common proper-subsystem bound can be grafted
with forests of the strictly shorter ambient pieces.
-/

namespace NSSE

universe u v

namespace ControlMonoid

noncomputable def nonzeroValuedWordForestStep
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    (zero : M)
    (hright : ∀ value : M, C.mul zero value = zero)
    (hleft : ∀ value : M, C.mul value zero = zero)
    (word : Word α) (hword : word ≠ [])
    (hnonzero : C.eval letter word ≠ zero)
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
        (innerBound + outerBound + 2)) := by
  let target :=
    max (3 * elements.normalized.values.length)
      (innerBound + outerBound + 2)
  by_cases hshort :
      word.length + 1 ≤
        3 * elements.normalized.values.length
  · exact
      (C.shortSimonStepForest
        elements letter word hword hshort).weaken
          target (Nat.le_max_left _ _)
  · have hlong :
        3 * elements.normalized.values.length <
          word.length + 1 := by
      omega
    let cuts :=
      Classical.choice
        (C.exists_fourPrefixControlCuts
          elements letter word hlong)
    have h01 := cuts.lt₀₁
    have h12 := cuts.lt₁₂
    have h23 := cuts.lt₂₃
    have hi3 := cuts.i₃_le
    have hproper :
        (C.rightStabilizer cuts.anchor).Proper :=
      cuts.rightStabilizer_proper_of_nonzero_total
        hright hleft hnonzero
    let indices := [cuts.i₀, cuts.i₁, cuts.i₂, cuts.i₃]
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
      simp [indices, blocksBetweenCuts] at hblock
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
          (properUniform cuts.anchor hproper)
          replacement)
    have hwhole :
        word.take cuts.i₀ ++
            (ControlMonoid.blocksBetweenCuts
              word indices).flatten ++
            word.drop cuts.i₃ =
          word := by
      simpa [indices, blocksBetweenCuts,
        List.append_assoc] using cuts.three_block_word_eq
    let assembled :=
      FactorTree.HeightBoundedForest.surround
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
    exact assembled.weaken target
      (Nat.le_max_right _ _)

end ControlMonoid

end NSSE
