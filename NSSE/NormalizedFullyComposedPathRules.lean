import NSSE.NormalizedResponseEmissionBatches
import NSSE.FullyComposedSemanticRealization

/-!
# Normalized response-path edges are fully composed unary rules
-/

namespace NSSE

universe u

theorem fullyComposed_unary_arity
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
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass) :
    1 ∈
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        ).arities := by
  apply
    (fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal).kind_arity_mem_allArities
        CompilerTagKind.side
  simp [fullyComposedRuleTests, CompilerTagRuleTests.merge,
    attachmentResponseRuleTests]

theorem FullyComposedTerminalFact.fullyComposed_terminal_true
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
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    (fact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal state) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).terminal state = true := by
  cases fact with
  | nonidentity =>
      rename_i loopId hloop hnonidentity
      change
        (fullyComposedRuleTests summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal).dispatchTerminal state = true
      unfold fullyComposedRuleTests
      rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
      apply Or.inl
      apply (finiteLoop_dispatchTerminal_iff summaryOf state).2
      refine ⟨loopId, ?_, ?_⟩ <;> assumption
  | guard control cutValue query hsolved =>
      change
        (fullyComposedRuleTests summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal).dispatchTerminal
            (.bounded control cutValue (.inl query)) = true
      unfold fullyComposedRuleTests
      rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
        CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
      exact Or.inr (Or.inr (by
        simpa [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] using hsolved))
  | «local» control cutValue localId hterminal =>
      change
        (fullyComposedRuleTests summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal).dispatchTerminal
            (.bounded control cutValue (.inr localId)) = true
      unfold fullyComposedRuleTests
      rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
        CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
      exact Or.inr (Or.inr (by
        simpa [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] using hterminal))

theorem fullyComposed_strictNormalizedPath_enabled
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
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    (hstrict :
      ∃ control cutValue parentInterval childInterval,
        parent = .side control cutValue parentInterval ∧
        child.interval? = some childInterval ∧
        SideDelegation parentInterval childInterval attachment ∧
        childInterval.span < parentInterval.span) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).enabled parent [child] = true := by
  obtain ⟨control, cutValue, parentInterval, childInterval,
    rfl, hinterval, hdelegates, _⟩ := hstrict
  change
    (fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal).dispatchEnabled
        (.side control cutValue parentInterval) [child] = true
  rw [fullyComposed_side_dispatchEnabled_iff]
  refine ⟨child, rfl, Or.inl ?_⟩
  unfold intervalSideEnabled
  rw [hinterval]
  exact (sideDelegationB_correct
    parentInterval childInterval attachment).2 hdelegates

theorem fullyComposed_registeredNormalizedPath_enabled
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
    (edges :
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
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hedge : edge ∈ edges) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).enabled
        (.side edge.control edge.cut edge.parent) [edge.child] = true := by
  change
    (fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges)
      localTerminal).dispatchEnabled
        (.side edge.control edge.cut edge.parent) [edge.child] = true
  rw [fullyComposed_side_dispatchEnabled_iff]
  exact ⟨edge.child, rfl, Or.inr
    ((attachmentResponseTableEnabled_eq_true_iff
      edges edge.control edge.cut edge.parent edge.child).2 hedge)⟩

theorem NormalizedResponseEmissionBatches.fullyComposed_labelledLiftable
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
    (edges :
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
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)
        atomCount queryCount → Bool)
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment edges source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches labels path
        guardedBatches forbiddenBatches)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal)
    (initialGuarded initialForbidden : List Bool)
    (hguardedLength : initialGuarded.length = atomCount)
    (hforbiddenLength : initialForbidden.length = queryCount)
    (hallowed :
      terminalAllowed
        ⟨GeneralizedState.mk terminal
            (markBatches guardedBatches initialGuarded)
            (markBatches forbiddenBatches initialForbidden),
          by
            constructor
            · rw [markBatches_length, hguardedLength]
            · rw [markBatches_length, hforbiddenLength]⟩ = true) :
    ∃ derive :
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros wires loops locals quotient
          ).TaggedDerives source,
      LabelledLiftable
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount queryCount terminalAllowed labels derive
        initialGuarded initialForbidden := by
  apply hemissions.labelledLiftable
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient)
    atomCount queryCount terminalAllowed
  · exact fullyComposed_unary_arity
      summaryOf attachment I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
  · exact terminalFact.fullyComposed_terminal_true
      summaryOf attachment I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
  · intro parent child hstrict
    exact fullyComposed_strictNormalizedPath_enabled
      summaryOf attachment I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient hstrict
  · intro edge hedge
    exact fullyComposed_registeredNormalizedPath_enabled
      summaryOf attachment I left right rightFinal event w j t
      edges localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      edge hedge
  · exact hallowed
  · exact hguardedLength
  · exact hforbiddenLength

theorem NormalizedResponseEmissionBatches.fullyComposed_decide_of_covered
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
    (edges :
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
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        List Nat)
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment edges source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches labels path
        guardedBatches forbiddenBatches)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal)
    (initialGuarded initialForbidden : List Bool)
    (hguardedLength : initialGuarded.length = atomCount)
    (hforbiddenLength :
      initialForbidden.length = queries.values.length)
    (hguardedCovered :
      RequirementsCovered initialGuarded guardedBatches
        (guardedRequired terminal))
    (hforbiddenCovered :
      RequirementsCovered initialForbidden forbiddenBatches
        (allCanonicalQueryIndices queries))
    (hguardedBounded :
      ∀ index ∈ guardedRequired terminal,
        index < initialGuarded.length) :
    ∃ index,
      index <
          (requiredLabelledGeneralizedStateRuleSystem
            (fullyComposedRuleSystem summaryOf attachment
              I left right rightFinal event w j t
              (attachmentResponseTableEnabled edges) localTerminal
              ctl cut ori intervals macros wires loops locals quotient)
            atomCount queries.values.length
            (allCanonicalForbiddenRequirement queries guardedRequired)
            labels).states.stateCount ∧
        decideRequiredLabelledState
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled edges) localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          atomCount queries.values.length
          (allCanonicalForbiddenRequirement queries guardedRequired)
          labels index = true := by
  have hallowed :=
    allCanonicalForbiddenTerminal_of_covered
      queries guardedRequired atomCount terminal
      initialGuarded initialForbidden
      guardedBatches forbiddenBatches
      hguardedLength hforbiddenLength
      hguardedCovered hforbiddenCovered hguardedBounded
  obtain ⟨derive, lift⟩ :=
    hemissions.fullyComposed_labelledLiftable
      summaryOf attachment I left right rightFinal event w j t
      edges localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      atomCount queries.values.length
      (requiredMasksTerminal
        (allCanonicalForbiddenRequirement queries guardedRequired)
        atomCount queries.values.length)
      labels terminalFact
      initialGuarded initialForbidden
      hguardedLength hforbiddenLength hallowed
  obtain ⟨index, hdecode, hdecide⟩ :=
    lift.decideRequiredLabelled
  exact ⟨index,
    (requiredLabelledGeneralizedStateRuleSystem
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      atomCount queries.values.length
      (allCanonicalForbiddenRequirement queries guardedRequired)
      labels).states.decode_some_lt hdecode,
    hdecide⟩

end NSSE
