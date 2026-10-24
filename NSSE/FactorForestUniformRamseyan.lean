import NSSE.FactorForestSplitCandidate
import NSSE.UniformFactorForestBound
import NSSE.UniformRamseyanSplitBound

/-!
# Uniform Ramseyan splits extracted from uniform factor forests

The colored-rank construction turns every nonempty bounded factor forest
into a Ramseyan split.  The empty word is supplied by the distinct-cut
split and weakened to the same uniform height.
-/

namespace NSSE

universe u v

namespace UniformFactorForestBound

noncomputable def toUniformRamseyanSplitBound
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {bound : Nat}
    (uniform :
      UniformFactorForestBound.{u, v} C bound) :
    UniformRamseyanSplitBound.{u, v} C
      ((bound + 2) * elements.colorWidth) where
  split := by
    intro α letter word
    by_cases hword : word = []
    · subst word
      have hheight :
          1 ≤ (bound + 2) * elements.colorWidth := by
        have hwidth := elements.colorWidth_pos
        have hpositive :
            0 < (bound + 2) * elements.colorWidth :=
          Nat.mul_pos (by omega) hwidth
        omega
      exact ⟨(RamseyanSplit.byDistinctCuts
        C letter []).weaken
          ((bound + 2) * elements.colorWidth)
          (by simpa using hheight)⟩
    · obtain ⟨forest⟩ :=
        uniform.forest letter word hword
      exact ⟨forest.ramseyanSplit elements⟩

end UniformFactorForestBound

end NSSE
