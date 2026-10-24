import NSSE.FinitePrefixControlLoop
import NSSE.BoundedFactorForestAssembly

/-!
# Forest assembly for three repeated-prefix blocks

Four equal prefix controls produce three consecutive nonempty blocks.
Once recursive forests for the three shorter blocks are available, they
can always be joined by binary nodes at height cost two.  If their
ambient controls coincide at an idempotent, a single Simon idempotent
node costs only one level.
-/

namespace NSSE

universe u v

namespace ControlMonoid.FourPrefixControlCuts

variable {M : Type v} {α : Type u}
variable {C : ControlMonoid M} {letter : α → M}
variable {word : Word α} {bound : Nat}

def binaryMiddleForest
    (cuts : C.FourPrefixControlCuts letter word)
    (first :
      FactorTree.HeightBoundedForest C letter cuts.block₀₁ bound)
    (second :
      FactorTree.HeightBoundedForest C letter cuts.block₁₂ bound)
    (third :
      FactorTree.HeightBoundedForest C letter cuts.block₂₃ bound) :
    FactorTree.HeightBoundedForest C letter
      (cuts.block₀₁ ++ cuts.block₁₂ ++ cuts.block₂₃)
      (bound + 2) :=
  FactorTree.HeightBoundedForest.ternaryBinary
    first second third

def idempotentMiddleForest
    (cuts : C.FourPrefixControlCuts letter word)
    (first :
      FactorTree.HeightBoundedForest C letter cuts.block₀₁ bound)
    (second :
      FactorTree.HeightBoundedForest C letter cuts.block₁₂ bound)
    (third :
      FactorTree.HeightBoundedForest C letter cuts.block₂₃ bound)
    (value : M) (hvalue : C.Idempotent value)
    (hfirst : C.eval letter cuts.block₀₁ = value)
    (hsecond : C.eval letter cuts.block₁₂ = value)
    (hthird : C.eval letter cuts.block₂₃ = value) :
    FactorTree.HeightBoundedForest C letter
      (cuts.block₀₁ ++ cuts.block₁₂ ++ cuts.block₂₃)
      (bound + 1) := by
  apply FactorTree.HeightBoundedForest.ternaryIdempotent
    first second third value hvalue
  · unfold FactorTree.control
    rw [first.yield_eq]
    exact hfirst
  · unfold FactorTree.control
    rw [second.yield_eq]
    exact hsecond
  · unfold FactorTree.control
    rw [third.yield_eq]
    exact hthird

noncomputable def wholeIdempotentForest
    (cuts : C.FourPrefixControlCuts letter word)
    (beforeForest :
      word.take cuts.i₀ ≠ [] →
        FactorTree.HeightBoundedForest C letter
          (word.take cuts.i₀) bound)
    (first :
      FactorTree.HeightBoundedForest C letter cuts.block₀₁ bound)
    (second :
      FactorTree.HeightBoundedForest C letter cuts.block₁₂ bound)
    (third :
      FactorTree.HeightBoundedForest C letter cuts.block₂₃ bound)
    (afterForest :
      word.drop cuts.i₃ ≠ [] →
        FactorTree.HeightBoundedForest C letter
          (word.drop cuts.i₃) bound)
    (value : M) (hvalue : C.Idempotent value)
    (hfirst : C.eval letter cuts.block₀₁ = value)
    (hsecond : C.eval letter cuts.block₁₂ = value)
    (hthird : C.eval letter cuts.block₂₃ = value) :
    FactorTree.HeightBoundedForest C letter word (bound + 3) := by
  let middle :=
    cuts.idempotentMiddleForest
      first second third value hvalue hfirst hsecond hthird
  by_cases hbefore : word.take cuts.i₀ = []
  · by_cases hafter : word.drop cuts.i₃ = []
    · let raised := middle.weaken (bound + 3) (by omega)
      apply raised.rewriteWord word
      simpa [middle, hbefore, hafter, List.append_assoc] using
        cuts.three_block_word_eq
    · let afterRaised :=
        (afterForest hafter).weaken (bound + 1) (by omega)
      let joined :=
        FactorTree.HeightBoundedForest.binary middle afterRaised
      let raised := joined.weaken (bound + 3) (by omega)
      apply raised.rewriteWord word
      simpa [joined, middle, afterRaised, hbefore,
        List.append_assoc] using cuts.three_block_word_eq
  · by_cases hafter : word.drop cuts.i₃ = []
    · let beforeRaised :=
        (beforeForest hbefore).weaken (bound + 1) (by omega)
      let joined :=
        FactorTree.HeightBoundedForest.binary beforeRaised middle
      let raised := joined.weaken (bound + 3) (by omega)
      apply raised.rewriteWord word
      simpa [joined, middle, beforeRaised, hafter,
        List.append_assoc] using cuts.three_block_word_eq
    · let beforeRaised :=
        (beforeForest hbefore).weaken (bound + 1) (by omega)
      let leftJoined :=
        FactorTree.HeightBoundedForest.binary beforeRaised middle
      let afterRaised :=
        (afterForest hafter).weaken (bound + 2) (by omega)
      let joined :=
        FactorTree.HeightBoundedForest.binary leftJoined afterRaised
      let raised := joined.weaken (bound + 3) (by omega)
      apply raised.rewriteWord word
      simpa [raised, joined, leftJoined, middle, beforeRaised,
        afterRaised, List.append_assoc] using
          cuts.three_block_word_eq

noncomputable def wholeBinaryForest
    (cuts : C.FourPrefixControlCuts letter word)
    (beforeForest :
      word.take cuts.i₀ ≠ [] →
        FactorTree.HeightBoundedForest C letter
          (word.take cuts.i₀) bound)
    (first :
      FactorTree.HeightBoundedForest C letter cuts.block₀₁ bound)
    (second :
      FactorTree.HeightBoundedForest C letter cuts.block₁₂ bound)
    (third :
      FactorTree.HeightBoundedForest C letter cuts.block₂₃ bound)
    (afterForest :
      word.drop cuts.i₃ ≠ [] →
        FactorTree.HeightBoundedForest C letter
          (word.drop cuts.i₃) bound) :
    FactorTree.HeightBoundedForest C letter word (bound + 4) := by
  let middle := cuts.binaryMiddleForest first second third
  by_cases hbefore : word.take cuts.i₀ = []
  · by_cases hafter : word.drop cuts.i₃ = []
    · let raised := middle.weaken (bound + 4) (by
        omega)
      apply raised.rewriteWord word
      simpa [middle, hbefore, hafter, List.append_assoc] using
        cuts.three_block_word_eq
    · let afterRaised :=
        (afterForest hafter).weaken (bound + 2) (by omega)
      let joined :=
        FactorTree.HeightBoundedForest.binary middle afterRaised
      let raised := joined.weaken (bound + 4) (by
        omega)
      apply raised.rewriteWord word
      simpa [joined, middle, afterRaised, hbefore,
        List.append_assoc] using cuts.three_block_word_eq
  · by_cases hafter : word.drop cuts.i₃ = []
    · let beforeRaised :=
        (beforeForest hbefore).weaken (bound + 2) (by omega)
      let joined :=
        FactorTree.HeightBoundedForest.binary beforeRaised middle
      let raised := joined.weaken (bound + 4) (by
        omega)
      apply raised.rewriteWord word
      simpa [joined, middle, beforeRaised, hafter,
        List.append_assoc] using cuts.three_block_word_eq
    · let beforeRaised :=
        (beforeForest hbefore).weaken (bound + 2) (by omega)
      let leftJoined :=
        FactorTree.HeightBoundedForest.binary beforeRaised middle
      let afterRaised :=
        (afterForest hafter).weaken (bound + 3) (by omega)
      let joined :=
        FactorTree.HeightBoundedForest.binary leftJoined afterRaised
      apply joined.rewriteWord word
      simpa [joined, leftJoined, middle, beforeRaised,
        afterRaised, List.append_assoc] using
          cuts.three_block_word_eq

end ControlMonoid.FourPrefixControlCuts

end NSSE
