import NSSE.FullyComposedRegisteredCoverage
import NSSE.NumberedRuleSystemGame

/-!
# Unary game handler for the normalized refined compiler

This packages the complete enabled-move classification as the witness
handler expected by the finite reachability-game soundness theorem.
-/

namespace NSSE

universe u

theorem fullyComposed_requiredLabelled_unaryMeaning
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (queries : Enumeration Query)
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    (atomCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (meaning :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length →
      Prop)
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length)
    (henabled :
      (requiredLabelledGeneralizedStateRuleSystem
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled
            (nonSideResponseEdges originalEdges))
          localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount queries.values.length requirement
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges queriesOf)).enabled
          parent [child] = true)
    (childMeaning : meaning child)
    (decreasingMeaning :
      NatPairLexLt
          (fullyComposedProgressMeasure
            atomCount queries.values.length child.1)
          (fullyComposedProgressMeasure
            atomCount queries.values.length parent.1) →
        meaning child →
        meaning parent)
    (registeredMeaning :
      ∀ edge ∈ nonSideResponseEdges originalEdges,
        parent.1.tag =
            .side edge.control edge.cut edge.parent →
        child.1.tag = edge.child →
        (∀ query ∈ queriesOf edge,
          maskBit parent.1.forbidden
            (enumerationIndex queries query) = true) →
        meaning child →
        meaning parent) :
    meaning parent := by
  let labels :=
    normalizedResponseTableFirstEventTransitionMaskLabels
      queries originalEdges queriesOf
  have hparts :=
    (requiredLabelled_enabled_iff
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      atomCount queries.values.length requirement labels
      parent [child]).1 henabled
  have hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent.1 [child.1] = true := by
    simpa using hparts.2
  have hcases :=
    fullyComposed_unary_enabled_progress_cases
      summaryOf attachment I left right rightFinal event w j t
      (attachmentResponseTableEnabled
        (nonSideResponseEdges originalEdges))
      localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      atomCount queries.values.length requirement labels
      parent child henabled
  exact fullyComposed_unaryMeaning_of_progress_cases
    summaryOf attachment queries originalEdges queriesOf
    atomCount meaning parent child hfollow hcases childMeaning
    decreasingMeaning registeredMeaning

theorem fullyComposed_allWitnessGameDecision_sound
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (queries : Enumeration Query)
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    (atomCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (meaning :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length →
      Prop)
    (terminalMeaning :
      ∀ state,
        (requiredLabelledGeneralizedStateRuleSystem
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges originalEdges))
            localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          atomCount queries.values.length requirement
          (normalizedResponseTableFirstEventTransitionMaskLabels
            queries originalEdges queriesOf)).terminal state = true →
        meaning state)
    (decreasingMeaning :
      ∀ parent child,
        NatPairLexLt
            (fullyComposedProgressMeasure
              atomCount queries.values.length child.1)
            (fullyComposedProgressMeasure
              atomCount queries.values.length parent.1) →
          meaning child →
          meaning parent)
    (registeredMeaning :
      ∀ parent child,
        ∀ edge ∈ nonSideResponseEdges originalEdges,
          parent.1.tag =
              .side edge.control edge.cut edge.parent →
          child.1.tag = edge.child →
          (∀ query ∈ queriesOf edge,
            maskBit parent.1.forbidden
              (enumerationIndex queries query) = true) →
          meaning child →
          meaning parent)
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
          atomCount queries.values.length requirement
          (normalizedResponseTableFirstEventTransitionMaskLabels
            queries originalEdges queriesOf)).states.stateCount)
    (haccept :
      ((requiredLabelledGeneralizedStateRuleSystem
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges originalEdges))
            localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          atomCount queries.values.length requirement
          (normalizedResponseTableFirstEventTransitionMaskLabels
            queries originalEdges queriesOf)).unaryGame
        (fun _ => true)).decideWinning index = true) :
    ∃ state,
      (requiredLabelledGeneralizedStateRuleSystem
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled
            (nonSideResponseEdges originalEdges))
          localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount queries.values.length requirement
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges queriesOf)).states.decode index =
          some state ∧
      meaning state := by
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      atomCount queries.values.length requirement
      (normalizedResponseTableFirstEventTransitionMaskLabels
        queries originalEdges queriesOf)
  apply system.allWitnessUnaryGameDecision_sound
    meaning terminalMeaning
  · intro parent child henabled hchild
    exact fullyComposed_requiredLabelled_unaryMeaning
      summaryOf attachment I left right rightFinal event w j t
      originalEdges localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      queries queriesOf atomCount requirement meaning
      parent child henabled hchild
      (decreasingMeaning parent child)
      (registeredMeaning parent child)
  · exact hindex
  · exact haccept

end NSSE
