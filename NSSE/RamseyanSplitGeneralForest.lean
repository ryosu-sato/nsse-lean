import NSSE.RamseyanTopBoundaryForest

/-!
# General conversion from Ramseyan splits to factorization forests

Induction on the split height combines the lower-height core forests between
top cuts, the common idempotent top span, and the two outside boundaries.
The resulting explicit forest-height bound is five times the split height.
-/

namespace NSSE

universe u v

namespace RamseyanSplit

noncomputable def toFactorForest
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} (height : Nat)
    (split : RamseyanSplit C letter word height)
    (hword : word ≠ []) :
    FactorTree.HeightBoundedForest C letter word
      (5 * height) := by
  induction height generalizing word with
  | zero =>
      exact False.elim
        (not_nonempty_height_zero
          C letter word ⟨split⟩)
  | succ height ih =>
      by_cases hused :
          ∃ cut : WordCut word,
            (split.rank cut).1 = height
      · have htopNonempty :
            split.topCuts ≠ [] :=
          (split.topCuts_nonempty_iff).2 hused
        cases hcutsValue : split.topCuts with
        | nil =>
            exact False.elim
              (htopNonempty hcutsValue)
        | cons first rest =>
            cases rest with
            | nil =>
                let built :=
                  split.wholeForest_of_one_topCut
                    first hcutsValue hword
                    (fun lowerSplit hlowerWord =>
                      ih lowerSplit hlowerWord)
                exact built.weaken (5 * Nat.succ height)
                  (by omega)
            | cons second rest =>
                let built :=
                  split.wholeForest_of_two_topCuts
                    first second rest hcutsValue
                    (fun lowerSplit hlowerWord =>
                      ih lowerSplit hlowerWord)
                exact built.weaken (5 * Nat.succ height)
                  (by omega)
      · let lowerSplit :=
          split.lowerOfTopUnused (by
            intro cut
            have hbound := (split.rank cut).2
            have hne :
                (split.rank cut).1 ≠ height := by
              intro heq
              exact hused ⟨cut, heq⟩
            omega)
        exact (ih lowerSplit hword).weaken
          (5 * Nat.succ height) (by omega)

end RamseyanSplit

namespace UniformRamseyanSplitBound

theorem toFactorForest
    (bounded :
      UniformRamseyanSplitBound.{u, v} C splitBound) :
    UniformFactorForestBound.{u, v}
      C (5 * splitBound) where
  forest := by
    intro α letter word hword
    obtain ⟨split⟩ := bounded.split letter word
    exact ⟨split.toFactorForest splitBound hword⟩

end UniformRamseyanSplitBound

end NSSE
