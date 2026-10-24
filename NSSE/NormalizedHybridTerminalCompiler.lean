import NSSE.FullyComposedHybridTerminalCompiler

/-!
# Normalized paths for the hybrid terminal compiler

An interval-bearing terminal satisfies the terminal-specific mask requirement
without any forbidden emission.  A non-interval terminal is reached through a
registered edge, so assigning every canonical query to every registered edge
supplies the full indexed forbidden mask.
-/

namespace NSSE

universe u

theorem NormalizedResponseEmissionBatches.fullyComposed_terminalSpecific_decide
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
          soa.indexedRootQueryEnumeration originalEdges
          (allQueriesOf soa.indexedRootQueryEnumeration))
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal) :
    ∃ index,
      index <
          (requiredLabelledGeneralizedStateRuleSystem
            (fullyComposedRuleSystem summaryOf attachment
              I left right rightFinal event w j t
              (attachmentResponseTableEnabled
                (nonSideResponseEdges originalEdges))
              localTerminal
              ctl cut ori intervals macros wires loops locals quotient)
            responseInitialMask.length
            soa.indexedRootQueryEnumeration.values.length
            (firstEventTerminalSpecificMaskRequirement
              soa.indexedRootQueryEnumeration)
            (normalizedResponseTableFirstEventTransitionMaskLabels
              soa.indexedRootQueryEnumeration originalEdges
              (allQueriesOf soa.indexedRootQueryEnumeration))
            ).states.stateCount ∧
        decideRequiredLabelledState
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled
              (nonSideResponseEdges originalEdges))
            localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          responseInitialMask.length
          soa.indexedRootQueryEnumeration.values.length
          (firstEventTerminalSpecificMaskRequirement
            soa.indexedRootQueryEnumeration)
          (normalizedResponseTableFirstEventTransitionMaskLabels
            soa.indexedRootQueryEnumeration originalEdges
            (allQueriesOf soa.indexedRootQueryEnumeration))
          index = true := by
  let initialGuarded :=
    List.replicate responseInitialMask.length false
  let initialForbidden :=
    List.replicate
      soa.indexedRootQueryEnumeration.values.length false
  have hguardedCovered :
      RequirementsCovered initialGuarded guardedBatches
        (firstEventGuardedRequirement terminal) :=
    hemissions.firstEventGuardedRequirementsCovered
      soa.indexedRootQueryEnumeration originalEdges
      (allQueriesOf soa.indexedRootQueryEnumeration)
      hsource initialGuarded
  let terminalState :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        responseInitialMask.length
        soa.indexedRootQueryEnumeration.values.length :=
    ⟨GeneralizedState.mk terminal
        (markBatches guardedBatches initialGuarded)
        (markBatches forbiddenBatches initialForbidden),
      by
        constructor
        · simp [initialGuarded, markBatches_length]
        · simp [initialForbidden, markBatches_length]⟩
  have hallowed :
      requiredMasksTerminal
        (firstEventTerminalSpecificMaskRequirement
          soa.indexedRootQueryEnumeration)
        responseInitialMask.length
        soa.indexedRootQueryEnumeration.values.length
        terminalState = true := by
    cases hinterval : terminalState.1.tag.interval? with
    | some interval =>
        change
          requiredMasksTerminal
            (terminalSpecificMaskRequirement
              soa.indexedRootQueryEnumeration firstEventGuardIndex)
            responseInitialMask.length
            soa.indexedRootQueryEnumeration.values.length
            terminalState = true
        exact
          requiredMasksTerminal_terminalSpecific_of_interval_some
            soa.indexedRootQueryEnumeration firstEventGuardIndex
            responseInitialMask.length terminalState hinterval
    | none =>
        change
          requiredMasksTerminal
            (terminalSpecificMaskRequirement
              soa.indexedRootQueryEnumeration firstEventGuardIndex)
            responseInitialMask.length
            soa.indexedRootQueryEnumeration.values.length
            terminalState = true
        rw [requiredMasksTerminal_terminalSpecific_of_interval_none
          soa.indexedRootQueryEnumeration firstEventGuardIndex
          responseInitialMask.length terminalState hinterval]
        have hterminalInterval : terminal.interval? = none := by
          simpa [terminalState] using hinterval
        change
          requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration
              firstEventGuardedRequirement)
            responseInitialMask.length
            soa.indexedRootQueryEnumeration.values.length
            ⟨GeneralizedState.mk terminal
                (markBatches guardedBatches initialGuarded)
                (markBatches forbiddenBatches initialForbidden),
              by
                constructor
                · simp [initialGuarded, markBatches_length]
                · simp [initialForbidden, markBatches_length]⟩ = true
        apply allCanonicalForbiddenTerminal_of_covered
          soa.indexedRootQueryEnumeration
          firstEventGuardedRequirement
          responseInitialMask.length terminal
          initialGuarded initialForbidden
          guardedBatches forbiddenBatches
        · simp [initialGuarded]
        · simp [initialForbidden]
        · exact hguardedCovered
        · apply allCanonicalRequirementsCovered_of_registeredEmission
            soa.indexedRootQueryEnumeration originalEdges
            (allQueriesOf soa.indexedRootQueryEnumeration)
            forbiddenBatches
          exact allCanonicalRegisteredEmission_of_complete
            soa.indexedRootQueryEnumeration originalEdges
            (allQueriesOf soa.indexedRootQueryEnumeration)
            forbiddenBatches
            (hemissions.completeRegisteredEmission_allQueriesOf
              soa.indexedRootQueryEnumeration originalEdges
              hsource hterminalInterval)
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
  obtain ⟨derive, lift⟩ :=
    hemissions.fullyComposed_labelledLiftable
      summaryOf attachment I left right rightFinal event w j t
      (nonSideResponseEdges originalEdges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      responseInitialMask.length
      soa.indexedRootQueryEnumeration.values.length
      (requiredMasksTerminal
        (firstEventTerminalSpecificMaskRequirement
          soa.indexedRootQueryEnumeration)
        responseInitialMask.length
        soa.indexedRootQueryEnumeration.values.length)
      (normalizedResponseTableFirstEventTransitionMaskLabels
        soa.indexedRootQueryEnumeration originalEdges
        (allQueriesOf soa.indexedRootQueryEnumeration))
      terminalFact initialGuarded initialForbidden
      (by simp [initialGuarded]) (by simp [initialForbidden])
      (by simpa [terminalState] using hallowed)
  obtain ⟨index, hdecode, hdecide⟩ :=
    lift.decideRequiredLabelled
  exact ⟨index,
    (requiredLabelledGeneralizedStateRuleSystem
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      responseInitialMask.length
      soa.indexedRootQueryEnumeration.values.length
      (firstEventTerminalSpecificMaskRequirement
        soa.indexedRootQueryEnumeration)
      (normalizedResponseTableFirstEventTransitionMaskLabels
        soa.indexedRootQueryEnumeration originalEdges
        (allQueriesOf soa.indexedRootQueryEnumeration))
      ).states.decode_some_lt hdecode,
    hdecide⟩

theorem NormalizedResponseEmissionBatches.fullyComposed_terminalSpecific_avoider
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
          soa.indexedRootQueryEnumeration originalEdges
          (allQueriesOf soa.indexedRootQueryEnumeration))
        path guardedBatches forbiddenBatches)
    (hsource : ∃ interval, source.interval? = some interval)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal)
    (realizer :
      FullyComposedTerminalSpecificRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        localTerminal) :
    ∃ word : Word β, soa.Avoider word := by
  obtain ⟨index, hindex, haccept⟩ :=
    hemissions.fullyComposed_terminalSpecific_decide
      soa summaryOf attachment I left right rightFinal event w j t
      originalEdges localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      hsource terminalFact
  exact realizer.decide_sound
    soa summaryOf attachment I left right rightFinal event w j t
    (attachmentResponseTableEnabled
      (nonSideResponseEdges originalEdges))
    localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    (normalizedResponseTableFirstEventTransitionMaskLabels
      soa.indexedRootQueryEnumeration originalEdges
      (allQueriesOf soa.indexedRootQueryEnumeration))
    index hindex haccept

end NSSE
