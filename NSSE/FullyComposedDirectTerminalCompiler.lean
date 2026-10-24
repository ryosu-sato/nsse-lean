import NSSE.FullyComposedIndexedMaskCompiler
import NSSE.LabelledGeneralizedStateCompleteness
import NSSE.FullyComposedSemanticRealization

/-!
# Fully composed terminals realized directly as avoiders

Some terminal facts already produce an avoider and therefore do not need a
full canonical forbidden mask.  This interface keeps those terminals
separate from candidate-only indexed-mask realizers.
-/

namespace NSSE

universe u

structure FullyComposedDirectTerminalRealizer
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
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass,
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal state →
      ∃ word : Word β, soa.Avoider word

namespace FullyComposedDirectTerminalRealizer

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
    (atomCount queryCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (realizer :
      FullyComposedDirectTerminalRealizer
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
          atomCount queryCount requirement labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount queryCount requirement labels index = true) :
    ∃ word : Word β, soa.Avoider word := by
  let base :=
    fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
  obtain ⟨state, _, derive⟩ :=
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).1
      haccept
  apply derive.sound
    (fun _ => ∃ word : Word β, soa.Avoider word)
  · intro terminalState hterminal
    have hparts :
        base.terminal terminalState.1.tag = true ∧
        requiredMasksTerminal requirement atomCount queryCount
          terminalState = true := by
      simpa [system, requiredLabelledGeneralizedStateRuleSystem,
        labelledGeneralizedStateRuleSystem,
        transitionGeneralizedStateRuleSystem] using hterminal
    apply realizer.realize terminalState.1.tag
    exact fullyComposed_terminal_implies_fact
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      terminalState.1.tag hparts.1
  · intro parent children henabled hchildren
    have hbase :
        base.enabled parent.1.tag
          (children.map fun child => child.1.tag) = true := by
      exact
        (requiredLabelled_enabled_iff
          base atomCount queryCount requirement labels
          parent children).1 henabled |>.1
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

theorem semantic_realize_noRequirement
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
    (atomCount queryCount : Nat)
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    (guarded forbidden : List Bool)
    (hvalid :
      (GeneralizedState.mk state guarded forbidden).Valid
        atomCount queryCount)
    (semantic :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal state)
    (realizer :
      FullyComposedDirectTerminalRealizer
        soa summaryOf attachment I left right rightFinal event w j t
        localEnabled localTerminal) :
    ∃ word : Word β, soa.Avoider word := by
  let base :=
    fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
  have derive : base.TaggedDerives state :=
    semantic.taggedDerives
      ctl cut ori intervals macros wires loops locals quotient
  obtain ⟨index, hdecode, haccept⟩ :=
    baseDerives_decideRequiredLabelled_noRequirement
      base atomCount queryCount labels derive
      guarded forbidden hvalid
  have hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount noTerminalMaskRequirement labels
          ).states.stateCount :=
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount noTerminalMaskRequirement labels
      ).states.decode_some_lt hdecode
  exact realizer.decide_sound
    soa summaryOf attachment I left right rightFinal event w j t
    localEnabled localTerminal
    ctl cut ori intervals macros wires loops locals quotient
    atomCount queryCount noTerminalMaskRequirement labels
    index hindex haccept

end FullyComposedDirectTerminalRealizer

end NSSE
