import NSSE.FiniteStructuralResponseHandler
import NSSE.FiniteMismatchResponseHandler

/-!
# Building long-forest handlers from fixed finite registries

The structural and mismatch registries share one fixed response edge
table and one fully composed rule system.  Their handler theorems fill
the two fields of `LongForestResponseHandlers`, completing the dispatch
from the long-forest response dichotomy to selected side roots.
-/

namespace NSSE

universe u

def longForestResponseHandlersOfRegistries
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
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros labels loops locals quotient)
      sideRoots C letter predicateCount where
  structural := by
    intro attachment emitter hendpoint
    exact structuralRegistry.handles_structural
      summaryOf domains I left right rightFinal event w j t
      ctl cut ori intervals macros labels loops locals quotient
      attachment emitter hendpoint
  mismatch := by
    intro attachment hmismatch
    exact mismatchRegistry.handles_mismatch
      summaryOf domains I left right rightFinal event w j t
      ctl cut ori intervals macros labels loops locals quotient
      attachment hmismatch

end NSSE
