import NSSE.NormalizedRegisteredEmissionCoverage
import NSSE.NormalizedFullyComposedPathRules
import NSSE.NormalizedFullyComposedIndexedMaskCompiler

/-!
# Guarded-index coverage along normalized response paths

A normalized path starting at an interval-bearing tag cannot terminate
reflexively at a bounded guard.  Its final transition into such a guard
therefore emits the guard's canonical first-event index.
-/

namespace NSSE

universe u

def firstEventGuardedRequirement
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (tag :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) : List Nat :=
  guardedIndicesOfCompilerTag firstEventGuardIndex tag

theorem NormalizedResponseEmissionBatches.guardIndex_emitted
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (originalEdges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges queriesOf)
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (control : Ctl) (cutValue : Cut)
    (query : FirstEventFiniteGuardQuery I left right event w j t)
    (hterminal :
      terminal = .bounded control cutValue (.inl query)) :
    ∃ batch ∈ guardedBatches,
      firstEventGuardIndex query ∈ batch := by
  induction hemissions with
  | refl state =>
      obtain ⟨interval, hinterval⟩ := hsource
      rw [hterminal] at hinterval
      simp [CompilerTag.interval?] at hinterval
  | @strict source child terminal head tail
      guardedBatches forbiddenBatches rest ih =>
      obtain ⟨_, _, _, childInterval, _, hchild, _, _⟩ := head
      obtain ⟨batch, hbatch, hindex⟩ :=
        ih ⟨childInterval, hchild⟩ hterminal
      exact ⟨batch, by simp [hbatch], hindex⟩
  | registered edge member =>
      refine
        ⟨(normalizedResponseTableFirstEventTransitionMaskLabels
            queries originalEdges queriesOf).guarded
            (.side edge.control edge.cut edge.parent) edge.child,
          by simp, ?_⟩
      rw [hterminal]
      simp [normalizedResponseTableFirstEventTransitionMaskLabels,
        responseTableFirstEventTransitionMaskLabels,
        canonicalFirstEventTransitionMaskLabels,
        firstEventTransitionMaskLabels,
        compilerTagTransitionMaskLabels,
        guardedIndicesOfCompilerTag]

theorem NormalizedResponseEmissionBatches.firstEventGuardedRequirementsCovered
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (originalEdges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges queriesOf)
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (initialGuarded : List Bool) :
    RequirementsCovered initialGuarded guardedBatches
      (firstEventGuardedRequirement terminal) := by
  intro index hindex
  cases terminal with
  | bounded control cutValue atom =>
      cases atom with
      | inl query =>
          simp [firstEventGuardedRequirement,
            guardedIndicesOfCompilerTag] at hindex
          subst index
          exact Or.inr
            (hemissions.guardIndex_emitted
              queries originalEdges queriesOf hsource
              control cutValue query rfl)
      | inr localId =>
          simp [firstEventGuardedRequirement,
            guardedIndicesOfCompilerTag] at hindex
  | nonstrong =>
      simp [firstEventGuardedRequirement,
        guardedIndicesOfCompilerTag] at hindex
  | side =>
      simp [firstEventGuardedRequirement,
        guardedIndicesOfCompilerTag] at hindex
  | strong =>
      simp [firstEventGuardedRequirement,
        guardedIndicesOfCompilerTag] at hindex
  | hub =>
      simp [firstEventGuardedRequirement,
        guardedIndicesOfCompilerTag] at hindex
  | copy =>
      simp [firstEventGuardedRequirement,
        guardedIndicesOfCompilerTag] at hindex

theorem NormalizedResponseEmissionBatches.completeRegisteredEmission_allQueriesOf
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (originalEdges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges (allQueriesOf queries))
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (hterminal : terminal.interval? = none) :
    CompleteRegisteredEmission
      queries originalEdges (allQueriesOf queries) forbiddenBatches := by
  induction hemissions with
  | refl state =>
      obtain ⟨interval, hinterval⟩ := hsource
      rw [hterminal] at hinterval
      simp at hinterval
  | @strict source child terminal head tail
      guardedBatches forbiddenBatches rest ih =>
      obtain ⟨_, _, _, childInterval, _, hchild, _, _⟩ := head
      exact (ih ⟨childInterval, hchild⟩ hterminal).prepend _
  | registered edge member =>
      exact completeRegisteredEmission_registered
        queries originalEdges (allQueriesOf queries)
        edge member (mem_allQueriesOf queries edge)

theorem NormalizedResponseEmissionBatches.fullyComposed_decide_from_empty
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (queries : Enumeration Query)
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges queriesOf)
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal)
    (hforbidden :
      AllCanonicalRegisteredEmission
        queries originalEdges queriesOf forbiddenBatches) :
    ∃ index,
      index <
          (requiredLabelledGeneralizedStateRuleSystem
            (fullyComposedRuleSystem summaryOf attachment
              I left right rightFinal event w j t
              (attachmentResponseTableEnabled
                (nonSideResponseEdges originalEdges))
              localTerminal
              ctl cut ori intervals macros wires loops locals quotient)
            responseInitialMask.length queries.values.length
            (allCanonicalForbiddenRequirement queries
              firstEventGuardedRequirement)
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf)).states.stateCount ∧
        decideRequiredLabelledState
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges originalEdges))
            localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          responseInitialMask.length queries.values.length
          (allCanonicalForbiddenRequirement queries
            firstEventGuardedRequirement)
          (normalizedResponseTableFirstEventTransitionMaskLabels
            queries originalEdges queriesOf)
          index = true := by
  let initialGuarded :=
    List.replicate responseInitialMask.length false
  let initialForbidden :=
    List.replicate queries.values.length false
  have hguardedCovered :
      RequirementsCovered initialGuarded guardedBatches
        (firstEventGuardedRequirement terminal) :=
    hemissions.firstEventGuardedRequirementsCovered
      queries originalEdges queriesOf hsource initialGuarded
  have hforbiddenCovered :
      RequirementsCovered initialForbidden forbiddenBatches
        (allCanonicalQueryIndices queries) :=
    allCanonicalRequirementsCovered_of_registeredEmission
      queries originalEdges queriesOf forbiddenBatches
      hforbidden initialForbidden
  apply hemissions.fullyComposed_decide_of_covered
    summaryOf attachment I left right rightFinal event w j t
    (nonSideResponseEdges originalEdges) localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    queries responseInitialMask.length
    firstEventGuardedRequirement
    (normalizedResponseTableFirstEventTransitionMaskLabels
      queries originalEdges queriesOf)
    terminalFact initialGuarded initialForbidden
  · simp [initialGuarded]
  · simp [initialForbidden]
  · exact hguardedCovered
  · exact hforbiddenCovered
  · intro index hindex
    cases terminal with
    | bounded control cutValue atom =>
        cases atom with
        | inl query =>
            simp [firstEventGuardedRequirement,
              guardedIndicesOfCompilerTag] at hindex
            subst index
            simp [initialGuarded]
            exact firstEventGuardIndex_lt query
        | inr localId =>
            simp [firstEventGuardedRequirement,
              guardedIndicesOfCompilerTag] at hindex
    | nonstrong =>
        simp [firstEventGuardedRequirement,
          guardedIndicesOfCompilerTag] at hindex
    | side =>
        simp [firstEventGuardedRequirement,
          guardedIndicesOfCompilerTag] at hindex
    | strong =>
        simp [firstEventGuardedRequirement,
          guardedIndicesOfCompilerTag] at hindex
    | hub =>
        simp [firstEventGuardedRequirement,
          guardedIndicesOfCompilerTag] at hindex
    | copy =>
        simp [firstEventGuardedRequirement,
          guardedIndicesOfCompilerTag] at hindex

theorem NormalizedResponseEmissionBatches.fullyComposed_avoider_from_empty
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
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List (Fin soa.rows.length))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          soa.indexedRootQueryEnumeration originalEdges queriesOf)
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal)
    (hforbidden :
      AllCanonicalRegisteredEmission
        soa.indexedRootQueryEnumeration
        originalEdges queriesOf forbiddenBatches)
    (realizer :
      FullyComposedIndexedTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal responseInitialMask.length
        firstEventGuardedRequirement) :
    ∃ word : Word β, soa.Avoider word := by
  obtain ⟨index, hindex, haccept⟩ :=
    hemissions.fullyComposed_decide_from_empty
      summaryOf attachment I left right rightFinal event w j t
      originalEdges queriesOf localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      soa.indexedRootQueryEnumeration
      hsource terminalFact hforbidden
  exact realizer.decide_normalizedResponseTable_sound
    soa summaryOf attachment I left right rightFinal event w j t
    originalEdges queriesOf localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    responseInitialMask.length firstEventGuardedRequirement
    index hindex haccept

theorem NormalizedResponseEmissionBatches.fullyComposed_avoider_from_empty_of_complete
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
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List (Fin soa.rows.length))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          soa.indexedRootQueryEnumeration originalEdges queriesOf)
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal)
    (hcomplete :
      CompleteRegisteredEmission
        soa.indexedRootQueryEnumeration
        originalEdges queriesOf forbiddenBatches)
    (realizer :
      FullyComposedIndexedTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal responseInitialMask.length
        firstEventGuardedRequirement) :
    ∃ word : Word β, soa.Avoider word := by
  apply hemissions.fullyComposed_avoider_from_empty
    soa summaryOf attachment I left right rightFinal event w j t
    originalEdges queriesOf localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    hsource terminalFact
  · exact allCanonicalRegisteredEmission_of_complete
      soa.indexedRootQueryEnumeration
      originalEdges queriesOf forbiddenBatches hcomplete
  · exact realizer

end NSSE
