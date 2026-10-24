import NSSE.LongForestAttachment
import NSSE.BoundedLongSideRootCertificate

/-!
# Dispatching a long forest response to an initial side root

Long-forest extraction now has only two outcomes: a structural emitter
or a semantic insertion mismatch.  A concrete finite compiler supplies
registration handlers for those outcomes.  This file composes the
geometry/forest theorem with such handlers and returns the selected
initial side-root derivation required by the final certificate.
-/

namespace NSSE

universe u

structure LongForestResponseHandlers
    (system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Label Atom QClass))
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (C : ControlMonoid Wire) (letter : α → Wire)
    (predicateCount : Nat) where
  structural :
    ∀ (attachment : ForestWordAttachment α)
      (emitter :
        ContextualStructuralEmitter α Wire C letter
          predicateCount Ctl Cut Macro),
      emitter.singletonChain.finalState ≠
          emitter.emitter.sourceState →
      ∃ root ∈ sideRoots,
        root.parent = attachment.parent ∧
          system.TaggedDerives
            (.side root.control root.cut root.parent)
  mismatch :
    ∀ attachment : ForestWordAttachment α,
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      Word.insertAt ordered.base attachment.payload ordered.leftSlot ≠
        Word.insertAt ordered.base attachment.payload
          ordered.rightSlot) →
      ∃ root ∈ sideRoots,
        root.parent = attachment.parent ∧
          system.TaggedDerives
            (.side root.control root.cut root.parent)

namespace LongForestResponseHandlers

theorem extract_from_long_forest
    [DecidableEq α]
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Label Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {C : ControlMonoid Wire} {letter : α → Wire}
    {word : Word α} {bound : Nat}
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      LongForestResponseHandlers system sideRoots
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
      handlers.structural attachment emitter hendpoint
    exact ⟨root, hroot, hderive⟩
  · obtain ⟨root, hroot, hparent, hderive⟩ :=
      handlers.mismatch attachment hmismatch
    exact ⟨root, hroot, hderive⟩

theorem extract_long_minimal_avoider
    [DecidableEq α]
    {I : SOAInstance α}
    {system :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori NatInterval Macro Label Atom QClass)}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {C : ControlMonoid Wire} {letter : α → Wire}
    {heightBound : Nat}
    {predicates : List UnaryArithmeticPredicate}
    (handlers :
      LongForestResponseHandlers system sideRoots
        C letter predicates.length)
    (forestOf :
      ∀ word : Word α, I.LengthMinimalAvoider word →
        FactorTree.HeightBoundedForest
          C letter word heightBound)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∀ word, I.LengthMinimalAvoider word →
      2 ^ heightBound < word.length →
      ∃ root ∈ sideRoots,
        system.TaggedDerives
          (.side root.control root.cut root.parent) := by
  intro word hminimal hlong
  exact handlers.extract_from_long_forest
    (forestOf word hminimal) hlong
    payload hpayload intervalChildren wireOf strongWire
    control cut macroData

end LongForestResponseHandlers

end NSSE
