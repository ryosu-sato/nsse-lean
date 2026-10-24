import NSSE.FactorForestRelabeling
import NSSE.UniformFactorForestBound

/-!
# Reduction of the uniform Simon theorem to the control alphabet

Every presented word has a positionwise control-value word.  A bounded
factorization forest for that word over alphabet `M`, with the identity letter
map, can be relabelled back to the original alphabet without changing its
height or Simon invariants.  Hence it is sufficient to prove the uniform
theorem for words over the finite control type itself.
-/

namespace NSSE

universe u v

structure ControlValueFactorForestBound
    (C : ControlMonoid M) (bound : Nat) : Prop where
  forest :
    ∀ word : Word M, word ≠ [] →
      Nonempty
        (FactorTree.HeightBoundedForest
          C id word bound)

namespace Aligned

theorem map_left
    (function : α → β) (word : Word α) :
    Aligned (fun value source => value = function source)
      (word.map function) word := by
  induction word with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons rfl ih

end Aligned

namespace ControlValueFactorForestBound

theorem toUniform
    (controlValues :
      ControlValueFactorForestBound C bound) :
    UniformFactorForestBound.{u, v} C bound where
  forest := by
    intro α letter word hword
    have hcontrolWord :
        word.map letter ≠ [] := by
      simpa using hword
    obtain ⟨controlForest⟩ :=
      controlValues.forest (word.map letter) hcontrolWord
    have haligned :
        Aligned
          (fun value symbol => id value = letter symbol)
          (word.map letter) word := by
      simpa using Aligned.map_left letter word
    exact controlForest.relabel_of_yield_aligned
      C haligned

theorem ofUniform
    (uniform :
      UniformFactorForestBound.{v, v} C bound) :
    ControlValueFactorForestBound C bound where
  forest := by
    intro word hword
    exact uniform.forest id word hword

theorem iff_uniform_same_universe :
    ControlValueFactorForestBound C bound ↔
      UniformFactorForestBound.{v, v} C bound := by
  constructor
  · exact toUniform
  · exact ofUniform

end ControlValueFactorForestBound

end NSSE
