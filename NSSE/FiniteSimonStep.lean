import NSSE.ThreePrefixBlockForest
import NSSE.FiniteFactorForestSearch

/-!
# One finite-control Simon decomposition step

At normalized control size `N`, a word is either short enough for its
canonical binary forest to have height at most `3N`, or its prefix
control sequence contains four equal values.  In the latter case the
three intervening nonempty blocks lie in one right stabilizer.  That
stabilizer is either proper (strict finite-size descent) or the anchor is
right absorbing and idempotent.
-/

namespace NSSE

universe u v

namespace ControlMonoid

inductive SimonStep
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α) : Type (max u v)
  | short
      (heightBound :
        word.length + 1 ≤
          3 * elements.normalized.values.length)
  | properStabilizer
      (cuts : FourPrefixControlCuts C letter word)
      (proper :
        (C.rightStabilizer cuts.anchor).Proper)
      (size_lt :
        ((C.rightStabilizer cuts.anchor).enumeration elements
          ).normalized.values.length <
          elements.normalized.values.length)
  | absorbingIdempotent
      (cuts : FourPrefixControlCuts C letter word)
      (idempotent : C.Idempotent cuts.anchor)
      (absorbing :
        ∀ value : M, C.mul cuts.anchor value = cuts.anchor)

noncomputable def finiteSimonStep
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α) :
    SimonStep C elements letter word := by
  by_cases hshort :
      word.length + 1 ≤
        3 * elements.normalized.values.length
  · exact .short hshort
  · have hlong :
        3 * elements.normalized.values.length <
          word.length + 1 := by omega
    let cuts :=
      Classical.choice
        (C.exists_fourPrefixControlCuts elements letter word hlong)
    by_cases hproper :
        (C.rightStabilizer cuts.anchor).Proper
    · exact .properStabilizer cuts hproper
        (C.rightStabilizer_normalized_length_lt
          elements cuts.anchor hproper)
    · exact .absorbingIdempotent cuts
        (C.idempotent_of_not_rightStabilizer_proper
          cuts.anchor hproper)
        (C.right_absorbing_of_not_stabilizer_proper
          cuts.anchor hproper)

def shortSimonStepForest
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hnonempty : word ≠ [])
    (hshort :
      word.length + 1 ≤
        3 * elements.normalized.values.length) :
    FactorTree.HeightBoundedForest C letter word
      (3 * elements.normalized.values.length) where
  tree := FactorTree.binaryOfWord word hnonempty
  isForest := FactorTree.binaryOfWord_isForest
    C letter word hnonempty
  yield_eq := FactorTree.binaryOfWord_yield word hnonempty
  height_le := by
    have hheight :=
      FactorTree.binaryOfWord_height_lt_length
        word hnonempty
    omega

theorem shortSimonStep_search_success
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hnonempty : word ≠ [])
    (hshort :
      word.length + 1 ≤
        3 * elements.normalized.values.length) :
    (findHeightBoundedForest?
      alphabet C letter word
      (3 * elements.normalized.values.length)).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  let forest :=
    C.shortSimonStepForest
      elements letter word hnonempty hshort
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

theorem equalIdempotentSimonStep_search_success
    [DecidableEq α] [DecidableEq M]
    (alphabet : Enumeration α)
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (cuts : C.FourPrefixControlCuts letter word)
    (bound : Nat)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest C letter subword bound)
    (value : M) (hvalue : C.Idempotent value)
    (hfirst : C.eval letter cuts.block₀₁ = value)
    (hsecond : C.eval letter cuts.block₁₂ = value)
    (hthird : C.eval letter cuts.block₂₃ = value) :
    (findHeightBoundedForest?
      alphabet C letter word (bound + 3)).isSome = true := by
  rw [findHeightBoundedForest_isSome_iff]
  let forest :=
    cuts.wholeIdempotentForest
      (fun hnonempty =>
        recursive (word.take cuts.i₀)
          cuts.before_length_lt hnonempty)
      (recursive cuts.block₀₁
        cuts.block₀₁_length_lt cuts.block₀₁_ne_nil)
      (recursive cuts.block₁₂
        cuts.block₁₂_length_lt cuts.block₁₂_ne_nil)
      (recursive cuts.block₂₃
        cuts.block₂₃_length_lt cuts.block₂₃_ne_nil)
      (fun hnonempty =>
        recursive (word.drop cuts.i₃)
          cuts.after_length_lt hnonempty)
      value hvalue hfirst hsecond hthird
  exact ⟨forest.tree, forest.isForest,
    forest.yield_eq, forest.height_le⟩

end ControlMonoid

end NSSE
