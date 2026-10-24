import NSSE.FactorForestUniformRamseyan
import NSSE.RamseyanSplitGeneralForest

/-!
# Bounded one-letter rotation of a factor forest

The factor-forest-to-split conversion lets us restrict to the suffix after
the first letter without recursively cutting Simon nodes by hand.  Converting
that restricted split back to a forest and appending the original head gives
a uniform forest for the one-step cyclic rotation.
-/

namespace NSSE

universe u v

def factorForestRotationBound
    [DecidableEq M]
    (elements : Enumeration M) (bound : Nat) : Nat :=
  5 * ((bound + 2) * elements.colorWidth) + 1

namespace FactorTree.HeightBoundedForest

noncomputable def rotateHeadToEnd
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (letter : α → M)
    (head : α) (tail : Word α) {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter (head :: tail) bound) :
    FactorTree.HeightBoundedForest
      C letter (tail ++ [head])
      (factorForestRotationBound elements bound) := by
  by_cases htail : tail = []
  · subst tail
    exact forest.weaken
      (factorForestRotationBound elements bound)
      (by
        unfold factorForestRotationBound
        have hwidth := elements.colorWidth_pos
        have hmul :=
          Nat.mul_le_mul_left (bound + 2)
            (show 1 ≤ elements.colorWidth by omega)
        simp only [Nat.mul_one] at hmul
        omega)
  · let split := forest.ramseyanSplit elements
    let left : WordCut (head :: tail) :=
      ⟨1, by simp⟩
    let right : WordCut (head :: tail) :=
      ⟨(head :: tail).length, by omega⟩
    have hle : left.1 ≤ right.1 := by
      simp [left, right,
        List.length_pos_iff.mpr htail]
    have hinterval :
        WordCut.interval
            (head :: tail) left right =
          tail := by
      unfold WordCut.interval
        ControlMonoid.middleFactor
      simp [left, right]
    let suffixSplit :=
      split.restrict left right hle
    have hsuffixNonempty :
        WordCut.interval
            (head :: tail) left right ≠ [] := by
      rw [hinterval]
      exact htail
    let suffixForest :=
      suffixSplit.toFactorForest
        ((bound + 2) * elements.colorWidth)
        hsuffixNonempty
    let suffixRewritten :=
      suffixForest.rewriteWord tail hinterval
    let headForest :=
      (FactorTree.HeightBoundedForest.leaf
        C letter head).weaken
          (5 * ((bound + 2) *
            elements.colorWidth)) (by omega)
    exact FactorTree.HeightBoundedForest.binary
      suffixRewritten headForest

noncomputable def rotateEndToHead
    [DecidableEq M]
    (elements : Enumeration M)
    (C : ControlMonoid M) (letter : α → M)
    (init : Word α) (last : α) {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter (init ++ [last]) bound) :
    FactorTree.HeightBoundedForest
      C letter (last :: init)
      (factorForestRotationBound elements bound) := by
  by_cases hinit : init = []
  · subst init
    exact forest.weaken
      (factorForestRotationBound elements bound)
      (by
        unfold factorForestRotationBound
        have hwidth := elements.colorWidth_pos
        have hmul :=
          Nat.mul_le_mul_left (bound + 2)
            (show 1 ≤ elements.colorWidth by omega)
        simp only [Nat.mul_one] at hmul
        omega)
  · let split := forest.ramseyanSplit elements
    let left : WordCut (init ++ [last]) :=
      ⟨0, by omega⟩
    let right : WordCut (init ++ [last]) :=
      ⟨init.length, by simp; omega⟩
    have hle : left.1 ≤ right.1 := by
      simp [left, right]
    have hinterval :
        WordCut.interval
            (init ++ [last]) left right =
          init := by
      unfold WordCut.interval
        ControlMonoid.middleFactor
      simp [left, right]
    let prefixSplit :=
      split.restrict left right hle
    have hprefixNonempty :
        WordCut.interval
            (init ++ [last]) left right ≠ [] := by
      rw [hinterval]
      exact hinit
    let prefixForest :=
      prefixSplit.toFactorForest
        ((bound + 2) * elements.colorWidth)
        hprefixNonempty
    let prefixRewritten :=
      prefixForest.rewriteWord init hinterval
    let lastForest :=
      (FactorTree.HeightBoundedForest.leaf
        C letter last).weaken
          (5 * ((bound + 2) *
            elements.colorWidth)) (by omega)
    exact FactorTree.HeightBoundedForest.binary
      lastForest prefixRewritten

end FactorTree.HeightBoundedForest

end NSSE
