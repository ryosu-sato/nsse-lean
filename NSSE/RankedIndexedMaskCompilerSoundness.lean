import NSSE.RankedFullyComposedRuleSoundness
import NSSE.FullyComposedSemanticPath
import NSSE.IndexedRootMaskCompilerSoundness

/-!
# Indexed forbidden-mask soundness for the ranked compiler
-/

namespace NSSE

theorem rankedFullyComposed_terminal_implies_fact
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (hterminal :
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height
        localEnabled localTerminal ctl cut ori macros wires loops
        locals quotient).terminal state = true) :
    FullyComposedTerminalFact summaryOf I left right rightFinal
      event w j t localTerminal state := by
  change
    (rankedFullyComposedRuleTests summaryOf
      I left right rightFinal event w j t height
      localEnabled localTerminal).dispatchTerminal state = true
    at hterminal
  unfold rankedFullyComposedRuleTests at hterminal
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff] at hterminal
  rcases hterminal with hloop | hresponse | hatomic
  · obtain ⟨loopId, hloopId, hnonidentity⟩ :=
      (finiteLoop_dispatchTerminal_iff summaryOf state).1 hloop
    exact .nonidentity state loopId hloopId hnonidentity
  · simp [attachmentResponseRuleTests,
      CompilerTagRuleTests.dispatchTerminal] at hresponse
  · cases state with
    | nonstrong =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hatomic
    | strong =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hatomic
    | hub =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hatomic
    | copy =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hatomic
    | side =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hatomic
    | bounded control cutValue atom =>
        cases atom with
        | inl query =>
            exact .guard control cutValue query (by
              simpa [unifiedAtomicRuleTests,
                CompilerTagRuleTests.dispatchTerminal] using hatomic)
        | inr localId =>
            exact .local control cutValue localId (by
              simpa [unifiedAtomicRuleTests,
                CompilerTagRuleTests.dispatchTerminal] using hatomic)

theorem rankedFullyComposed_enabled_children_ne_nil
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (parent :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (children :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (henabled :
      (rankedFullyComposedRuleTests summaryOf
        I left right rightFinal event w j t height
        localEnabled localTerminal).dispatchEnabled
          parent children = true) :
    children ≠ [] := by
  have harity :=
    ((rankedFullyComposedRuleTests summaryOf
      I left right rightFinal event w j t height
      localEnabled localTerminal).dispatchEnabled_correct
        parent children).1 henabled
  intro hnil
  subst children
  cases parent <;>
    simp [rankedFullyComposedRuleTests, CompilerTagRuleTests.merge,
      finiteLoopRuleTests, attachmentResponseRuleTests,
      unifiedAtomicRuleTests, CompilerTag.kind] at harity

structure RankedFullyComposedIndexedTerminalRealizer
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localTerminal : LocalId → Bool)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      List Nat) where
  realize :
    ∀ state :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)
        atomCount soa.indexedRootQueryEnumeration.values.length,
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal state.1.tag →
      requiredMasksTerminal
          (allCanonicalForbiddenRequirement
            soa.indexedRootQueryEnumeration guardedRequired)
          atomCount soa.indexedRootQueryEnumeration.values.length
          state = true →
      ∃ word : Word β,
        soa.candidate word ∧
        soa.IndexedMaskForbids state.1.forbidden word

namespace RankedFullyComposedIndexedTerminalRealizer

theorem decide_sound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      List Nat)
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (realizer :
      RankedFullyComposedIndexedTerminalRealizer
        soa summaryOf I left right rightFinal event w j t height
        localTerminal atomCount guardedRequired)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          (rankedFullyComposedRuleSystem summaryOf
            I left right rightFinal event w j t height
            localEnabled localTerminal ctl cut ori macros wires loops
            locals quotient)
          atomCount soa.indexedRootQueryEnumeration.values.length
          (allCanonicalForbiddenRequirement
            soa.indexedRootQueryEnumeration guardedRequired)
          labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        (rankedFullyComposedRuleSystem summaryOf
          I left right rightFinal event w j t height
          localEnabled localTerminal ctl cut ori macros wires loops
          locals quotient)
        atomCount soa.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          soa.indexedRootQueryEnumeration guardedRequired)
        labels index = true) :
    ∃ word : Word β, soa.Avoider word := by
  let base :=
    rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height
      localEnabled localTerminal ctl cut ori macros wires loops
      locals quotient
  apply decideIndexedRootMaskState_sound_of_nonempty_rules
    soa base atomCount guardedRequired labels
  · intro state hterminal hmasks
    apply realizer.realize state
    · exact rankedFullyComposed_terminal_implies_fact
        summaryOf I left right rightFinal event w j t height
        localEnabled localTerminal ctl cut ori macros wires loops
        locals quotient state.1.tag hterminal
    · exact hmasks
  · intro parent children henabled
    exact rankedFullyComposed_enabled_children_ne_nil
      summaryOf I left right rightFinal event w j t height
      localEnabled localTerminal parent children henabled
  · exact hindex
  · exact haccept

end RankedFullyComposedIndexedTerminalRealizer

end NSSE
