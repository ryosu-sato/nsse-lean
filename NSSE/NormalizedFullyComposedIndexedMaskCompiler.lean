import NSSE.FullyComposedIndexedMaskCompiler
import NSSE.FullyComposedSemanticRealization
import NSSE.LabelledGeneralizedStateCompleteness
import NSSE.NormalizedResponseForbiddenLabels

/-!
# The indexed-mask compiler specialized to a normalized response table

This removes the remaining choice of transition labels from the soundness
interface.  Local transitions are exactly the normalized non-side response
edges, and their forbidden labels are exactly the registered root queries.
-/

namespace NSSE

universe u

namespace FullyComposedIndexedTerminalRealizer

theorem decide_normalizedResponseTable_sound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass →
        List (Fin soa.rows.length))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        List Nat)
    (realizer :
      FullyComposedIndexedTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal atomCount guardedRequired)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges originalEdges))
            localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          atomCount soa.indexedRootQueryEnumeration.values.length
          (allCanonicalForbiddenRequirement
            soa.indexedRootQueryEnumeration guardedRequired)
          (normalizedResponseTableFirstEventTransitionMaskLabels
            soa.indexedRootQueryEnumeration
            originalEdges queriesOf)).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled
            (nonSideResponseEdges originalEdges))
          localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount soa.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          soa.indexedRootQueryEnumeration guardedRequired)
        (normalizedResponseTableFirstEventTransitionMaskLabels
          soa.indexedRootQueryEnumeration
          originalEdges queriesOf)
        index = true) :
    ∃ word : Word β, soa.Avoider word := by
  exact realizer.decide_sound
    soa summaryOf attachment I left right rightFinal event w j t
    (attachmentResponseTableEnabled
      (nonSideResponseEdges originalEdges))
    localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    atomCount guardedRequired
    (normalizedResponseTableFirstEventTransitionMaskLabels
      soa.indexedRootQueryEnumeration originalEdges queriesOf)
    index hindex haccept

end FullyComposedIndexedTerminalRealizer

theorem FullyComposedSemantic.decide_normalized_saturated
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass →
        List (Fin soa.rows.length))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        List Nat)
    (hguarded :
      ∀ tag index, index ∈ guardedRequired tag →
        index < atomCount)
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    (semantic :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal state) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled
            (nonSideResponseEdges originalEdges))
          localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount soa.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          soa.indexedRootQueryEnumeration guardedRequired)
        (normalizedResponseTableFirstEventTransitionMaskLabels
          soa.indexedRootQueryEnumeration originalEdges queriesOf)
        ).states.decode index =
          some
            ⟨GeneralizedState.mk state
                (List.replicate atomCount true)
                (List.replicate
                  soa.indexedRootQueryEnumeration.values.length true),
              by simp [GeneralizedState.Valid]⟩ ∧
      decideRequiredLabelledState
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled
            (nonSideResponseEdges originalEdges))
          localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount soa.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          soa.indexedRootQueryEnumeration guardedRequired)
        (normalizedResponseTableFirstEventTransitionMaskLabels
          soa.indexedRootQueryEnumeration originalEdges queriesOf)
        index = true := by
  apply baseDerives_decideRequiredLabelled_saturated
  · intro tag index hindex
    exact hguarded tag index hindex
  · intro tag index hindex
    exact allCanonicalQueryIndices_bounded
      soa.indexedRootQueryEnumeration index hindex
  · exact semantic.taggedDerives
      ctl cut ori intervals macros wires loops locals quotient

end NSSE
