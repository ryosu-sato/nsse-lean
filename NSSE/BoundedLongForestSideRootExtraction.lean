import NSSE.LongForestAttachment
import NSSE.BoundedAttachmentResponseDispatcher
import NSSE.SemanticTaggedRootFamily
import NSSE.GroupPaletteFactorForest

/-!
# Long-forest extraction into a word-bounded compiler

Absolute interval coordinates are finite for one fixed source word.
An extracted attachment has `parent.stop ≤ word.length`, so its semantic
parent has a canonical code in `BoundedNatInterval word.length`.
-/

namespace NSSE

universe u

structure BoundedInitialSideRoot
    (limit : Nat) (Ctl Cut : Type) where
  control : Ctl
  cut : Cut
  parent : BoundedNatInterval limit
deriving DecidableEq

namespace BoundedInitialSideRoot

def toInitialSideRoot
    (root : BoundedInitialSideRoot limit Ctl Cut) :
    InitialSideRoot Ctl Cut where
  control := root.control
  cut := root.cut
  parent := root.parent.toNatInterval

end BoundedInitialSideRoot

def ForestWordAttachment.boundedParent
    (attachment : ForestWordAttachment α)
    {limit : Nat} (hupper : attachment.upper.length ≤ limit) :
    BoundedNatInterval limit :=
  BoundedNatInterval.ofNatInterval attachment.parent
    (Nat.le_trans attachment.parent_stop_le_upper_length hupper)

@[simp] theorem ForestWordAttachment.boundedParent_toNatInterval
    (attachment : ForestWordAttachment α)
    {limit : Nat} (hupper : attachment.upper.length ≤ limit) :
    (attachment.boundedParent hupper).toNatInterval =
      attachment.parent := by
  exact BoundedNatInterval.toNatInterval_ofNatInterval
    attachment.parent _

structure WordBoundedLongForestResponseHandlers
    (word : Word α)
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (BoundedNatInterval word.length)
          Macro Label Atom QClass))
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (C : ControlMonoid Wire) (letter : α → Wire)
    (predicateCount : Nat) where
  structural :
    ∀ (attachment : ForestWordAttachment α)
      (_hupper : attachment.upper = word)
      (emitter :
        ContextualStructuralEmitter α Wire C letter
          predicateCount Ctl Cut Macro),
      emitter.singletonChain.finalState ≠
          emitter.emitter.sourceState →
      ∃ root ∈ sideRoots,
        root.parent.toNatInterval = attachment.parent ∧
          system.TaggedDerives
            (.side root.control root.cut root.parent)
  mismatch :
    ∀ (attachment : ForestWordAttachment α)
      (_hupper : attachment.upper = word),
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      Word.insertAt ordered.base attachment.payload ordered.leftSlot ≠
        Word.insertAt ordered.base attachment.payload
          ordered.rightSlot) →
      ∃ root ∈ sideRoots,
        root.parent.toNatInterval = attachment.parent ∧
          system.TaggedDerives
            (.side root.control root.cut root.parent)

namespace WordBoundedLongForestResponseHandlers

theorem extract_from_long_forest
    [DecidableEq α]
    {word : Word α} {bound : Nat}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori (BoundedNatInterval word.length)
          Macro Label Atom QClass)}
    {sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut)}
    {C : ControlMonoid Wire} {letter : α → Wire}
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      WordBoundedLongForestResponseHandlers word system sideRoots
        C letter predicates.length)
    (forest :
      FactorTree.HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ root ∈ sideRoots,
      system.TaggedDerives
        (.side root.control root.cut root.parent) := by
  obtain ⟨attachment, hupper, hmiddle, hresponse⟩ :=
    forest.exists_attachment_structural_or_mismatch
      hlong payload hpayload intervalChildren predicates
      wireOf strongWire control cut macroData
  dsimp only at hresponse
  rcases hresponse with hstructural | hmismatch
  · obtain ⟨emitter, hendpoint⟩ := hstructural
    obtain ⟨root, hroot, hparent, hderive⟩ :=
      handlers.structural attachment hupper emitter hendpoint
    exact ⟨root, hroot, hderive⟩
  · obtain ⟨root, hroot, hparent, hderive⟩ :=
      handlers.mismatch attachment hupper hmismatch
    exact ⟨root, hroot, hderive⟩

theorem exists_uniform_extract_long_minimal_avoider
    {M α : Type u}
    [DecidableEq M] [DecidableEq α]
    {I : SOAInstance α}
    (systems :
      ∀ word : Word α,
        NumberedRuleSystem
          (CompilerTag Ctl Cut Ori (BoundedNatInterval word.length)
            Macro Label Atom QClass))
    (roots :
      ∀ word : Word α,
        List (BoundedInitialSideRoot word.length Ctl Cut))
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M)
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      ∀ word,
        WordBoundedLongForestResponseHandlers word
          (systems word) (roots word) C letter predicates.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → M)
    (strongWire : M)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ heightBound,
      ∀ word, I.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ root ∈ roots word,
          (systems word).TaggedDerives
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
  exact (handlers word).extract_from_long_forest
    forest hlong payload hpayload intervalChildren
    wireOf strongWire control cut macroData

end WordBoundedLongForestResponseHandlers

end NSSE
