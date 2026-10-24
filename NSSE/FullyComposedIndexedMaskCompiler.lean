import NSSE.FullyComposedTerminalClassification
import NSSE.FullyComposedNonemptyRules
import NSSE.IndexedRootMaskCompilerSoundness

/-!
# Sound fully composed compiler with indexed forbidden masks

A terminal realizer supplies one representative candidate word for each
classified fully composed terminal under the current saturated mask.  The
generic mask soundness theorem and unary-rule theorem then turn executable
fixed-point acceptance into an actual SOA avoider.
-/

namespace NSSE

universe u

structure FullyComposedIndexedTerminalRealizer
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
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        List Nat) where
  realize :
    ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
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

namespace FullyComposedIndexedTerminalRealizer

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
    (realizer :
      FullyComposedIndexedTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal atomCount guardedRequired)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          (fullyComposedRuleSystem summaryOf attachment
            I left right rightFinal event w j t
            localEnabled localTerminal
            ctl cut ori intervals macros wires loops locals quotient)
          atomCount soa.indexedRootQueryEnumeration.values.length
          (allCanonicalForbiddenRequirement
            soa.indexedRootQueryEnumeration guardedRequired)
          labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount soa.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          soa.indexedRootQueryEnumeration guardedRequired)
        labels index = true) :
    ∃ word : Word β, soa.Avoider word := by
  apply decideIndexedRootMaskState_sound_of_nonempty_rules
    soa
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient)
    atomCount guardedRequired labels
  · intro state hterminal hmasks
    apply realizer.realize state
    · exact fullyComposed_terminal_implies_fact
        summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        state.1.tag hterminal
    · exact hmasks
  · exact fullyComposed_enabled_children_ne_nil
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
  · exact hindex
  · exact haccept

end FullyComposedIndexedTerminalRealizer

end NSSE
