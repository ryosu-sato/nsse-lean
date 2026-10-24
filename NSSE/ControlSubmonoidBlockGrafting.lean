import NSSE.FactorForestSubstitution
import NSSE.FiniteControlSubmonoid

/-!
# Grafting block forests from a control submonoid

In a stabilizer induction, a whole nonempty block is treated as one
letter of the smaller control monoid.  A forest over those block letters
can first be transported along the submonoid inclusion and then grafted
with ambient forests for the individual blocks.  This is the precise
interface needed to return from the smaller algebra to the original
word alphabet; no claim that the individual original letters belong to
the stabilizer is required.
-/

namespace NSSE

universe u v w

namespace ControlSubmonoid

def graftBlockForest
    {M : Type v} {α : Type u} {β : Type w}
    {C : ControlMonoid M}
    {symbols : Word β} {innerBound outerBound : Nat}
    (S : ControlSubmonoid C)
    (letter : α → M)
    (block : β → Word α)
    (block_mem :
      ∀ symbol, S.carrier (C.eval letter (block symbol)))
    (replacement :
      ∀ symbol,
        FactorTree.HeightBoundedForest
          C letter (block symbol) innerBound)
    (outer :
      FactorTree.HeightBoundedForest
        S.toControlMonoid
        (fun symbol =>
          ⟨C.eval letter (block symbol), block_mem symbol⟩)
        symbols outerBound) :
    FactorTree.HeightBoundedForest
      C letter (symbols.flatMap block)
        (innerBound + outerBound) := by
  let ambientOuter :
      FactorTree.HeightBoundedForest C
        (fun symbol => C.eval letter (block symbol))
        symbols outerBound :=
    S.inclusion_heightBoundedForest
      (fun symbol =>
        ⟨C.eval letter (block symbol), block_mem symbol⟩)
      outer
  let replacementControl :
      β → M :=
    fun symbol =>
      FactorTree.control C letter (replacement symbol).tree
  have hcontrol :
      ∀ symbol,
        replacementControl symbol =
          C.eval letter (block symbol) := by
    intro symbol
    unfold replacementControl FactorTree.control
    rw [(replacement symbol).yield_eq]
  have outerForGraft :
      FactorTree.HeightBoundedForest C
        replacementControl symbols outerBound := by
    have hletter :
        replacementControl =
          fun symbol => C.eval letter (block symbol) :=
      funext hcontrol
    refine {
      tree := ambientOuter.tree
      isForest := ?_
      yield_eq := ambientOuter.yield_eq
      height_le := ambientOuter.height_le
    }
    rw [hletter]
    exact ambientOuter.isForest
  exact FactorTree.HeightBoundedForest.graft
    C letter block replacement outerForGraft

end ControlSubmonoid

end NSSE
