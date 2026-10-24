import NSSE.NormalizedResponseEntryMembership
import NSSE.FiniteAttachmentResponseHandlers

/-!
# Long-forest handlers over the normalized response table

Structural and mismatch registries built for an arbitrary finite table can
be transported to its non-side-child normalization and then combined into
the long-forest handlers.  The resulting table satisfies the executable
path-normalization check by construction.
-/

namespace NSSE

universe u

def normalizedLongForestResponseHandlers
    [DecidableEq α]
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
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (labels : Enumeration Label)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (C : ControlMonoid ControlWire) (letter : α → ControlWire)
    (predicateCount : Nat)
    (structuralRegistry :
      FiniteStructuralResponseRegistry sideRoots edges
        (fullyComposedRuleSystem summaryOf domains
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros labels loops locals quotient)
        C letter predicateCount)
    (mismatchRegistry :
      FiniteMismatchResponseRegistry
        (α := α)
        (Guard :=
          FirstEventFiniteGuardQuery I left right event w j t)
        sideRoots edges localTerminal) :
    LongForestResponseHandlers
      (fullyComposedRuleSystem summaryOf domains
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges edges)) localTerminal
        ctl cut ori intervals macros labels loops locals quotient)
      sideRoots C letter predicateCount := by
  let normalizedStructural :=
    structuralRegistry.normalize
      summaryOf domains I left right rightFinal event w j t
      localTerminal ctl cut ori intervals macros labels loops locals
      quotient
  let normalizedMismatch := mismatchRegistry.normalize
  exact longForestResponseHandlersOfRegistries
    summaryOf domains I left right rightFinal event w j t
    sideRoots (nonSideResponseEdges edges) localTerminal
    ctl cut ori intervals macros labels loops locals quotient
    C letter predicateCount
    normalizedStructural normalizedMismatch

theorem normalizedResponseTable_checked
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Label LoopId
        Guard LocalId QClass)) :
    responseTableNonSideChildrenB
      (nonSideResponseEdges edges) = true :=
  nonSideResponseEdges_checked edges

end NSSE
