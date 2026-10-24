import NSSE.NormalizedHybridTerminalCompiler
import NSSE.NormalizedAttachmentResponseHandlers
import NSSE.BoundedLongSideRootCertificate

/-!
# Hybrid realization of normalized selected side roots

The semantic unary response of a selected side root normalizes to strict
interval descent followed by at most one registered non-side edge.  Its exact
transition labels supply the terminal-specific masks, so the hybrid terminal
realizer turns the path into an actual SOA avoider.
-/

namespace NSSE

universe u

theorem selectedSide_realize_by_normalizedHybrid
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (roots : List (InitialSideRoot Ctl Cut))
    (realizer :
      FullyComposedTerminalSpecificRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal) :
    ∀ root ∈ roots,
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal
        (.side root.control root.cut root.parent) →
      ∃ word : Word β, soa.Avoider word := by
  apply selectedSide_realize_of_normalized_table_paths
    (nonSideResponseEdges_checked originalEdges)
  intro root hroot terminal path terminalFact
  obtain ⟨guardedBatches, forbiddenBatches, hemissions⟩ :=
    path.exists_emissionBatches
      (normalizedResponseTableFirstEventTransitionMaskLabels
        soa.indexedRootQueryEnumeration originalEdges
        (allQueriesOf soa.indexedRootQueryEnumeration))
  exact hemissions.fullyComposed_terminalSpecific_avoider
    soa summaryOf attachment I left right rightFinal event w j t
    originalEdges localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    ⟨root.parent, rfl⟩ terminalFact realizer

def normalizedHybridSideRootRealizationSemantics
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (roots : List (InitialSideRoot Ctl Cut))
    (realizer :
      FullyComposedTerminalSpecificRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal) :
    InitialSideRootRealizationSemantics soa
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      roots := by
  apply fullyComposedSemanticSideRootRealization
    soa summaryOf attachment I left right rightFinal event w j t
    (attachmentResponseTableEnabled
      (nonSideResponseEdges originalEdges))
    localTerminal
    ctl cut ori intervals macros wires loops locals quotient roots
  exact selectedSide_realize_by_normalizedHybrid
    soa summaryOf attachment I left right rightFinal event w j t
    originalEdges localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    roots realizer

def normalizedHybridBoundedLongSideRootCertificate
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (boundedRoots :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (bound : Nat)
    (boundedExact :
      (∃ state ∈ boundedRoots,
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled
            (nonSideResponseEdges originalEdges))
          localTerminal
          ctl cut ori intervals macros wires loops locals quotient
          ).TaggedDerives state) ↔
        ∃ word : Word β,
          word.length ≤ bound ∧ soa.Avoider word)
    (extractLong :
      ∀ word, soa.LengthMinimalAvoider word →
        bound < word.length →
        ∃ root ∈ sideRoots,
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges originalEdges))
            localTerminal
            ctl cut ori intervals macros wires loops locals quotient
            ).TaggedDerives
              (.side root.control root.cut root.parent))
    (realizer :
      FullyComposedTerminalSpecificRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal) :
    BoundedLongSideRootCertificate soa
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      boundedRoots sideRoots bound where
  bounded_exact := boundedExact
  extract_long := extractLong
  realize_side :=
    (normalizedHybridSideRootRealizationSemantics
      soa summaryOf attachment I left right rightFinal event w j t
      originalEdges localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      sideRoots realizer).realize

end NSSE
