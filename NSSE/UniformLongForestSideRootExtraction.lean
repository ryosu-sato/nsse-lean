import NSSE.GroupPaletteFactorForest
import NSSE.LongForestSideRootExtraction

/-!
# Uniform Simon forests in long-side-root extraction

The long-word hypothesis already implies that the candidate word is
nonempty.  We can therefore instantiate the uniform Simon theorem exactly
where the long-forest response theorem needs a forest, without requiring
an impossible forest for a potentially empty minimal avoider.
-/

namespace NSSE

universe u

namespace LongForestResponseHandlers

theorem exists_uniform_extract_long_minimal_avoider
    {M α : Type u}
    [DecidableEq M] [DecidableEq α]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Label Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      LongForestResponseHandlers system sideRoots
        C letter predicates.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → M)
    (strongWire : M)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ heightBound,
      ∀ word, I.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ root ∈ sideRoots,
          system.TaggedDerives
            (.side root.control root.cut root.parent) := by
  obtain ⟨heightBound, uniform⟩ :=
    exists_uniformFactorForestBound C elements
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  have hword : word ≠ [] := by
    intro hempty
    subst word
    simp at hlong
  let forest :=
    Classical.choice
      (uniform.forest letter word hword)
  exact handlers.extract_from_long_forest
    forest hlong payload hpayload intervalChildren
    wireOf strongWire control cut macroData

theorem exists_boundedLongSideRootCertificate
    {M α : Type u}
    [DecidableEq M] [DecidableEq α]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Label Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      LongForestResponseHandlers system sideRoots
        C letter predicates.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → M)
    (strongWire : M)
    (control : Ctl) (cut : Cut) (macroData : Macro)
    (boundedRoots :
      Nat →
        List
          (CompilerTag Ctl Cut Ori NatInterval
            Macro Label Atom QClass))
    (boundedExact :
      ∀ bound,
        (∃ state ∈ boundedRoots bound,
          system.TaggedDerives state) ↔
        ∃ word : Word α,
          word.length ≤ bound ∧ I.Avoider word)
    (realizeSide :
      (∃ root ∈ sideRoots,
        system.TaggedDerives
          (.side root.control root.cut root.parent)) →
        ∃ word : Word α, I.Avoider word) :
    ∃ bound,
      BoundedLongSideRootCertificate I system
        (boundedRoots bound) sideRoots bound := by
  obtain ⟨heightBound, extractLong⟩ :=
    handlers.exists_uniform_extract_long_minimal_avoider
      C elements letter payload hpayload
      intervalChildren wireOf strongWire
      control cut macroData
  let bound := 2 ^ heightBound
  exact ⟨bound, {
    bounded_exact := boundedExact bound
    extract_long := by
      intro word hminimal hlong
      exact extractLong word hminimal hlong
    realize_side := realizeSide
  }⟩

end LongForestResponseHandlers

end NSSE
