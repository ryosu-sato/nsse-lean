import NSSE.LongForestAttachment
import NSSE.RankedAttachmentResponseDispatcher
import NSSE.GroupPaletteFactorForest

/-!
# Long-forest extraction into a fixed ranked compiler

Selected roots store finite ranks.  A separate relation records which
semantic attachment parents each rank realizes; this relation is not
part of the finite compiler state.
-/

namespace NSSE

universe u

structure RankedInitialSideRoot
    (height : Nat) (Ctl Cut : Type) where
  control : Ctl
  cut : Cut
  rank : SideRank height
deriving DecidableEq

structure RankedLongForestResponseHandlers
    (height : Nat)
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Label Atom QClass))
    (sideRoots : List (RankedInitialSideRoot height Ctl Cut))
    (realizes : SideRank height → NatInterval → Prop)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (predicateCount : Nat) where
  structural :
    ∀ (attachment : ForestWordAttachment α)
      (emitter :
        ContextualStructuralEmitter α Wire C letter
          predicateCount Ctl Cut Macro),
      emitter.singletonChain.finalState ≠ emitter.emitter.sourceState →
      ∃ root ∈ sideRoots,
        realizes root.rank attachment.parent ∧
          system.TaggedDerives
            (.side root.control root.cut root.rank)
  mismatch :
    ∀ attachment : ForestWordAttachment α,
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      Word.insertAt ordered.base attachment.payload ordered.leftSlot ≠
        Word.insertAt ordered.base attachment.payload
          ordered.rightSlot) →
      ∃ root ∈ sideRoots,
        realizes root.rank attachment.parent ∧
          system.TaggedDerives
            (.side root.control root.cut root.rank)

namespace RankedLongForestResponseHandlers

theorem extract_from_long_forest
    [DecidableEq α]
    {height : Nat}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Label Atom QClass)}
    {sideRoots : List (RankedInitialSideRoot height Ctl Cut)}
    {realizes : SideRank height → NatInterval → Prop}
    {C : ControlMonoid Wire} {letter : α → Wire}
    {word : Word α} {bound : Nat}
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      RankedLongForestResponseHandlers height system sideRoots realizes
        C letter predicates.length)
    (forest : FactorTree.HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ attachment : ForestWordAttachment α,
      attachment.upper = word ∧
      ∃ root ∈ sideRoots,
        realizes root.rank attachment.parent ∧
        system.TaggedDerives
          (.side root.control root.cut root.rank) := by
  obtain ⟨attachment, hupper, hmiddle, hresponse⟩ :=
    forest.exists_attachment_structural_or_mismatch
      hlong payload hpayload intervalChildren predicates
      wireOf strongWire control cut macroData
  dsimp only at hresponse
  refine ⟨attachment, hupper, ?_⟩
  rcases hresponse with hstructural | hmismatch
  · obtain ⟨emitter, hendpoint⟩ := hstructural
    exact handlers.structural attachment emitter hendpoint
  · exact handlers.mismatch attachment hmismatch

theorem exists_uniform_extract_long_minimal_avoider
    {M α : Type u}
    [DecidableEq M] [DecidableEq α]
    {I : SOAInstance α}
    {height : Nat}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (SideRank height)
          Macro Label Atom QClass)}
    {sideRoots : List (RankedInitialSideRoot height Ctl Cut)}
    {realizes : SideRank height → NatInterval → Prop}
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      RankedLongForestResponseHandlers height system sideRoots realizes
        C letter predicates.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → M)
    (strongWire : M)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ heightBound,
      ∀ word, I.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ attachment : ForestWordAttachment α,
          attachment.upper = word ∧
          ∃ root ∈ sideRoots,
            realizes root.rank attachment.parent ∧
            system.TaggedDerives
              (.side root.control root.cut root.rank) := by
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

end RankedLongForestResponseHandlers

end NSSE
