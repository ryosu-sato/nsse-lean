import NSSE.TerminalSpecificMaskRequirement
import NSSE.FullyComposedDirectTerminalCompiler

/-!
# Hybrid direct/indexed terminal realization

Interval terminals use a direct avoider witness.  Non-interval terminals
use the indexed canonical-forbidden mask.  The terminal-specific
requirement makes these two interfaces compatible in one compiler.
-/

namespace NSSE

universe u

structure FullyComposedTerminalSpecificRealizer
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
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool) where
  realize :
    ∀ state :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)
        responseInitialMask.length
        soa.indexedRootQueryEnumeration.values.length,
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal state.1.tag →
      requiredMasksTerminal
          (firstEventTerminalSpecificMaskRequirement
            soa.indexedRootQueryEnumeration)
          responseInitialMask.length
          soa.indexedRootQueryEnumeration.values.length state = true →
      ∃ word : Word β, soa.Avoider word

def fullyComposedHybridTerminalRealizer
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
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (direct :
      FullyComposedDirectTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal)
    (indexed :
      FullyComposedIndexedTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal responseInitialMask.length
        firstEventGuardedRequirement) :
    FullyComposedTerminalSpecificRealizer
      soa summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal where
  realize := by
    intro state fact hmasks
    cases hinterval : state.1.tag.interval? with
    | some interval =>
        exact direct.realize state.1.tag fact
    | none =>
        have hall :
            requiredMasksTerminal
              (allCanonicalForbiddenRequirement
                soa.indexedRootQueryEnumeration
                firstEventGuardedRequirement)
              responseInitialMask.length
              soa.indexedRootQueryEnumeration.values.length state =
                true := by
          change
            requiredMasksTerminal
              (terminalSpecificMaskRequirement
                soa.indexedRootQueryEnumeration firstEventGuardIndex)
              responseInitialMask.length
              soa.indexedRootQueryEnumeration.values.length state =
                true at hmasks
          rw [requiredMasksTerminal_terminalSpecific_of_interval_none
            soa.indexedRootQueryEnumeration
            firstEventGuardIndex responseInitialMask.length
            state hinterval] at hmasks
          exact hmasks
        obtain ⟨word, hcandidate, hforbids⟩ :=
          indexed.realize state fact hall
        exact ⟨word,
          soa.avoider_of_allCanonicalMaskTerminal
            firstEventGuardedRequirement responseInitialMask.length
            state word hall
            hcandidate hforbids⟩

namespace FullyComposedTerminalSpecificRealizer

theorem decide_sound
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
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (realizer :
      FullyComposedTerminalSpecificRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            localEnabled localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          responseInitialMask.length
          soa.indexedRootQueryEnumeration.values.length
          (firstEventTerminalSpecificMaskRequirement
            soa.indexedRootQueryEnumeration)
          labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        responseInitialMask.length
        soa.indexedRootQueryEnumeration.values.length
        (firstEventTerminalSpecificMaskRequirement
          soa.indexedRootQueryEnumeration)
        labels index = true) :
    ∃ word : Word β, soa.Avoider word := by
  let base :=
    fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
  obtain ⟨state, _, derive⟩ :=
    (decideRequiredLabelledState_correct
      base responseInitialMask.length
      soa.indexedRootQueryEnumeration.values.length
      (firstEventTerminalSpecificMaskRequirement
        soa.indexedRootQueryEnumeration)
      labels index hindex).1 haccept
  apply derive.sound
    (fun _ => ∃ word : Word β, soa.Avoider word)
  · intro terminalState hterminal
    have hparts :
        base.terminal terminalState.1.tag = true ∧
        requiredMasksTerminal
          (firstEventTerminalSpecificMaskRequirement
            soa.indexedRootQueryEnumeration)
          responseInitialMask.length
          soa.indexedRootQueryEnumeration.values.length
          terminalState = true := by
      simpa [requiredLabelledGeneralizedStateRuleSystem,
        labelledGeneralizedStateRuleSystem,
        transitionGeneralizedStateRuleSystem] using hterminal
    apply realizer.realize terminalState
    · exact fullyComposed_terminal_implies_fact
        summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        terminalState.1.tag hparts.1
    · exact hparts.2
  · intro parent children henabled hchildren
    have hbase :
        base.enabled parent.1.tag
          (children.map fun child => child.1.tag) = true :=
      ((requiredLabelled_enabled_iff
        base responseInitialMask.length
        soa.indexedRootQueryEnumeration.values.length
        (firstEventTerminalSpecificMaskRequirement
          soa.indexedRootQueryEnumeration)
        labels parent children).1 henabled).1
    have htags :
        (children.map fun child => child.1.tag) ≠ [] :=
      fullyComposed_enabled_children_ne_nil
        summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        parent.1.tag
        (children.map fun child => child.1.tag) hbase
    cases children with
    | nil =>
        exact False.elim (htags rfl)
    | cons child rest =>
        exact hchildren child (by simp)

end FullyComposedTerminalSpecificRealizer

end NSSE
