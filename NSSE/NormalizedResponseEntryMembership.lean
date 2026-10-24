import NSSE.FiniteResponsePathNormalization
import NSSE.FiniteStructuralResponseHandler
import NSSE.FiniteMismatchResponseHandler

/-!
# Structural and mismatch entries survive response-table normalization

Structural entries now explicitly record the loop ID carried by their
child.  Mismatch entries always target a bounded child.  Hence both kinds
of registered response remain present after filtering side-child edges.
-/

namespace NSSE

universe u

namespace FiniteStructuralResponseEntry

theorem edge_mem_nonSideResponseEdges
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    {attachment : ForestWordAttachment α}
    {emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        Guard LocalId QClass)}
    {system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Label LoopId
          (UnifiedAtomicId Guard LocalId) QClass)}
    (entry :
      FiniteStructuralResponseEntry attachment emitter
        sideRoots edges system) :
    ({
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.parent
      child := entry.child
    } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
      Guard LocalId QClass) ∈ nonSideResponseEdges edges := by
  apply structuralEdge_mem_nonSideResponseEdges
    edges _ entry.child_loopId entry.child_loopId_eq
  exact entry.edge_mem

end FiniteStructuralResponseEntry

namespace FiniteStructuralResponseRegistry

def normalize
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (labels : Enumeration Label)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {C : ControlMonoid ControlWire} {letter : α → ControlWire}
    {predicateCount : Nat}
    (registry :
      FiniteStructuralResponseRegistry sideRoots edges
        (fullyComposedRuleSystem summaryOf domains
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros labels loops locals quotient)
        C letter predicateCount) :
    FiniteStructuralResponseRegistry sideRoots
      (nonSideResponseEdges edges)
      (fullyComposedRuleSystem summaryOf domains
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges edges)) localTerminal
        ctl cut ori intervals macros labels loops locals quotient)
      C letter predicateCount where
  entry := by
    intro attachment emitter hendpoint
    let oldEntry :=
      registry.entry attachment emitter hendpoint
    refine {
      endpoint_ne := oldEntry.endpoint_ne
      root := oldEntry.root
      root_mem := oldEntry.root_mem
      parent_eq := oldEntry.parent_eq
      child := oldEntry.child
      child_loopId := oldEntry.child_loopId
      child_loopId_eq := oldEntry.child_loopId_eq
      edge_mem := oldEntry.edge_mem_nonSideResponseEdges
      child_derives := ?_
    }
    exact fullyComposed_structural_derives_transfer
      summaryOf domains I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges)
      (attachmentResponseTableEnabled
        (nonSideResponseEdges edges))
      localTerminal localTerminal
      ctl cut ori intervals macros labels loops locals quotient
      oldEntry.child oldEntry.child_loopId
      oldEntry.child_loopId_eq oldEntry.child_derives

end FiniteStructuralResponseRegistry

namespace FiniteMismatchResponseEntry

theorem edge_mem_nonSideResponseEdges
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    {attachment : ForestWordAttachment α}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (entry :
      FiniteMismatchResponseEntry attachment sideRoots
        edges localTerminal) :
    ({
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.parent
      child := CompilerTag.bounded
        entry.root.control entry.root.cut (.inr entry.localId)
    } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
      Guard LocalId QClass) ∈ nonSideResponseEdges edges := by
  apply boundedEdge_mem_nonSideResponseEdges
  exact entry.edge_mem

def normalize
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    {attachment : ForestWordAttachment α}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (entry :
      FiniteMismatchResponseEntry attachment sideRoots
        edges localTerminal) :
    FiniteMismatchResponseEntry attachment sideRoots
      (nonSideResponseEdges edges) localTerminal where
  root := entry.root
  root_mem := entry.root_mem
  parent_eq := entry.parent_eq
  localId := entry.localId
  terminal_registered := entry.terminal_registered
  edge_mem := entry.edge_mem_nonSideResponseEdges

end FiniteMismatchResponseEntry

namespace FiniteMismatchResponseRegistry

def normalize
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (registry :
      FiniteMismatchResponseRegistry
        (α := α) sideRoots edges localTerminal) :
    FiniteMismatchResponseRegistry
      (α := α) sideRoots
      (nonSideResponseEdges edges) localTerminal where
  entry := fun attachment =>
    (registry.entry attachment).normalize

end FiniteMismatchResponseRegistry

end NSSE
