import NSSE.RamseyanTopCuts
import NSSE.RamseyanSplitFactorForest

/-!
# Forests for the interval between adjacent top cuts

The strict interior of adjacent top cuts has a split of one lower height.
After recursively constructing its forest, the two boundary letters are
restored with at most two binary levels.
-/

namespace NSSE

universe u v

namespace FactorTree.HeightBoundedForest

def singleton
    (C : ControlMonoid M) (letter : α → M)
    (value : α) (bound : Nat) :
    FactorTree.HeightBoundedForest
      C letter [value] bound where
  tree := .leaf value
  isForest := .leaf value
  yield_eq := by
    simp [FactorTree.yield]
  height_le := by
    simp [FactorTree.height]

end FactorTree.HeightBoundedForest

namespace RamseyanSplit

theorem topInterval_decomposition
    {word : Word α}
    (left right : WordCut word)
    (hwide : left.1 + 2 ≤ right.1) :
    [word[left.1]] ++
        WordCut.interval word
          (topCoreLeft left right hwide)
          (topCoreRight left right hwide) ++
        [word[right.1 - 1]] =
      WordCut.interval word left right := by
  let coreLeft := topCoreLeft left right hwide
  let coreRight := topCoreRight left right hwide
  have hleftCore :
      left.1 ≤ coreLeft.1 := by
    simp [coreLeft, topCoreLeft]
  have hcore :
      coreLeft.1 ≤ coreRight.1 :=
    topCoreLeft_le_right left right hwide
  have hcoreRight :
      coreRight.1 ≤ right.1 := by
    simp only [coreRight, topCoreRight]
    omega
  have hfirst :
      WordCut.interval word left coreLeft =
        [word[left.1]] := by
    have hleftBound : left.1 < word.length := by
      have hright := right.val_le_length
      omega
    simpa [coreLeft, topCoreLeft] using
      WordCut.interval_succ_eq_singleton
        word left.1 hleftBound
  have hlast :
      WordCut.interval word coreRight right =
        [word[right.1 - 1]] := by
    have hlastBound :
        right.1 - 1 < word.length := by
      have hright := right.val_le_length
      omega
    have hrightSucc :
        right.1 - 1 + 1 = right.1 := by
      omega
    simpa [coreRight, topCoreRight, hrightSucc] using
      WordCut.interval_succ_eq_singleton
        word (right.1 - 1) hlastBound
  calc
    [word[left.1]] ++
          WordCut.interval word coreLeft coreRight ++
          [word[right.1 - 1]] =
        WordCut.interval word left coreLeft ++
          WordCut.interval word coreLeft coreRight ++
          WordCut.interval word coreRight right := by
            rw [hfirst, hlast]
    _ = WordCut.interval word left coreRight ++
          WordCut.interval word coreRight right := by
            rw [WordCut.interval_append
              word left coreLeft coreRight
              hleftCore hcore]
    _ = WordCut.interval word left right := by
            exact WordCut.interval_append
              word left coreRight right
              (Nat.le_trans hleftCore hcore)
              hcoreRight

noncomputable def topIntervalForest_of_core
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (left right : WordCut word)
    (hwide : left.1 + 2 ≤ right.1)
    (core :
      FactorTree.HeightBoundedForest C letter
        (WordCut.interval word
          (topCoreLeft left right hwide)
          (topCoreRight left right hwide))
        bound) :
    FactorTree.HeightBoundedForest C letter
      (WordCut.interval word left right)
      (bound + 2) := by
  apply FactorTree.HeightBoundedForest.surround
    (beforeWord := [word[left.1]])
    (middleWord :=
      WordCut.interval word
        (topCoreLeft left right hwide)
        (topCoreRight left right hwide))
    (afterWord := [word[right.1 - 1]])
    (wholeWord := WordCut.interval word left right)
    core
    (fun _ =>
      FactorTree.HeightBoundedForest.singleton
        C letter word[left.1] bound)
    (fun _ =>
      FactorTree.HeightBoundedForest.singleton
        C letter word[right.1 - 1] bound)
  exact topInterval_decomposition left right hwide

noncomputable def topIntervalForest
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    {left right : WordCut word}
    (htop : split.TopNeighbors left right)
    (coreForest :
      ∀ hlong : left.1 + 3 ≤ right.1,
      FactorTree.HeightBoundedForest C letter
        (WordCut.interval word
          (topCoreLeft left right (by omega))
          (topCoreRight left right (by omega)))
        bound) :
    FactorTree.HeightBoundedForest C letter
      (WordCut.interval word left right)
      (bound + 2) := by
  by_cases hlong : left.1 + 3 ≤ right.1
  · exact topIntervalForest_of_core
      left right (by omega) (coreForest hlong)
  · have hnonempty :
        WordCut.interval word left right ≠ [] :=
      WordCut.interval_ne_nil word htop.1
    let tree :=
      FactorTree.binaryOfWord
        (WordCut.interval word left right) hnonempty
    exact {
      tree := tree
      isForest :=
        FactorTree.binaryOfWord_isForest
          C letter _ hnonempty
      yield_eq :=
        FactorTree.binaryOfWord_yield _ hnonempty
      height_le := by
        have hheight :=
          FactorTree.binaryOfWord_height_lt_length
            _ hnonempty
        have hlength :
            (WordCut.interval word left right).length =
              right.1 - left.1 :=
          ControlMonoid.middleFactor_length word
            (Nat.le_of_lt htop.1)
            right.val_le_length
        dsimp [tree]
        rw [hlength] at hheight
        omega
    }

noncomputable def topIntervalForest_of_lower
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    {left right : WordCut word}
    (htop : split.TopNeighbors left right)
    (lowerForest :
      ∀ {lowerWord : Word α},
        RamseyanSplit C letter lowerWord height →
        lowerWord ≠ [] →
        FactorTree.HeightBoundedForest
          C letter lowerWord bound) :
    FactorTree.HeightBoundedForest C letter
      (WordCut.interval word left right)
      (bound + 2) := by
  apply split.topIntervalForest htop
  intro hlong
  let lowerSplit :=
    split.topCoreSplit htop (by omega)
  exact lowerForest lowerSplit
    (topCore_interval_ne_nil left right hlong)

end RamseyanSplit

end NSSE
