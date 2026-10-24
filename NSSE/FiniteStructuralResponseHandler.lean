import NSSE.LongForestSideRootExtraction
import NSSE.RegisteredAttachmentResponseTable

/-!
# Finite-table handler for extracted structural emitters

A fixed compiler registers each relevant endpoint-changing structural
emitter as one response edge.  An entry records its selected side root,
the emitted child, edge membership, and the child's derivation in the
fixed fully composed system.  The dispatcher then derives the enclosing
side root.
-/

namespace NSSE

universe u

structure FiniteStructuralResponseEntry
    (attachment : ForestWordAttachment α)
    (emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro)
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        Guard LocalId QClass))
    (system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Label LoopId
          (UnifiedAtomicId Guard LocalId) QClass)) where
  endpoint_ne :
    emitter.singletonChain.finalState ≠ emitter.emitter.sourceState
  root : InitialSideRoot Ctl Cut
  root_mem : root ∈ sideRoots
  parent_eq : root.parent = attachment.parent
  child :
    FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Label LoopId
      (UnifiedAtomicId Guard LocalId) QClass
  child_loopId : LoopId
  child_loopId_eq : child.loopId? = some child_loopId
  edge_mem :
    ({
      control := root.control
      cut := root.cut
      parent := root.parent
      child := child
    } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
      Guard LocalId QClass) ∈ edges
  child_derives : system.TaggedDerives child

namespace FiniteStructuralResponseEntry

theorem side_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Label)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    {attachment : ForestWordAttachment α}
    {emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (labels : Enumeration Label)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (entry :
      FiniteStructuralResponseEntry attachment emitter sideRoots edges
        (fullyComposedRuleSystem summaryOf domains
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros labels loops locals quotient)) :
    (fullyComposedRuleSystem summaryOf domains
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros labels loops locals quotient
      ).TaggedDerives
        (.side entry.root.control entry.root.cut entry.root.parent) := by
  let edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass :=
    {
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.parent
      child := entry.child
    }
  apply fullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (attachment := domains)
    (I := I) (left := left) (right := right)
    (rightFinal := rightFinal)
    (event := event) (w := w) (j := j) (t := t)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori)
    (intervals := intervals) (macros := macros)
    (wires := labels) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := edge)
  · exact entry.edge_mem
  · exact entry.child_derives

end FiniteStructuralResponseEntry

structure FiniteStructuralResponseRegistry
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        Guard LocalId QClass))
    (system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Label LoopId
          (UnifiedAtomicId Guard LocalId) QClass))
    (C : ControlMonoid ControlWire) (letter : α → ControlWire)
    (predicateCount : Nat) where
  entry :
    ∀ (attachment : ForestWordAttachment α)
      (emitter :
        ContextualStructuralEmitter α ControlWire C letter
          predicateCount Ctl Cut Macro),
      emitter.singletonChain.finalState ≠
          emitter.emitter.sourceState →
      FiniteStructuralResponseEntry attachment emitter
        sideRoots edges system

namespace FiniteStructuralResponseRegistry

theorem handles_structural
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Label)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    {C : ControlMonoid ControlWire} {letter : α → ControlWire}
    {predicateCount : Nat}
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (labels : Enumeration Label)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (registry :
      FiniteStructuralResponseRegistry sideRoots edges
        (fullyComposedRuleSystem summaryOf domains
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros labels loops locals quotient)
        C letter predicateCount)
    (attachment : ForestWordAttachment α)
    (emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro)
    (hendpoint :
      emitter.singletonChain.finalState ≠ emitter.emitter.sourceState) :
    ∃ root ∈ sideRoots,
      root.parent = attachment.parent ∧
      (fullyComposedRuleSystem summaryOf domains
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros labels loops locals quotient
        ).TaggedDerives
          (.side root.control root.cut root.parent) := by
  let entry := registry.entry attachment emitter hendpoint
  exact ⟨entry.root, entry.root_mem, entry.parent_eq,
    entry.side_derives
      summaryOf domains I left right rightFinal event w j t
      ctl cut ori intervals macros labels loops locals quotient⟩

end FiniteStructuralResponseRegistry

end NSSE
