import NSSE.NormalizedAttachmentResponseHandlers

/-!
# Semantic induction over normalized finite response paths

A normalized response path contains only strict interval descent, except
possibly for one final registered table edge.  This file packages the
corresponding induction principle for semantic realization.

The three mathematical obligations are kept explicit:

* a terminal fact already at the current state;
* backward preservation across one strict interval descent;
* realization of the terminal fact after the final registered edge.
-/

namespace NSSE

universe u

theorem FullyComposedTerminalFact.meaning
    [DecidableEq QC] [DecidableEq QL]
    {summaryOf : LoopId → LoopSummary Wire}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {localTerminal : LocalId → Bool}
    (stateMeaning :
      FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (nonidentityMeaning :
      ∀ tag loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        stateMeaning tag)
    (guardMeaning :
      ∀ control cut query,
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true →
        stateMeaning (.bounded control cut (.inl query)))
    (localMeaning :
      ∀ control cut localId,
        localTerminal localId = true →
        stateMeaning (.bounded control cut (.inr localId)))
    {state}
    (fact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal state) :
    stateMeaning state := by
  cases fact with
  | nonidentity =>
      apply nonidentityMeaning <;> assumption
  | guard =>
      apply guardMeaning
      assumption
  | «local» =>
      apply localMeaning
      assumption

theorem NormalizedFiniteResponsePath.meaning
    [DecidableEq QC] [DecidableEq QL]
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (stateMeaning :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (terminalMeaning :
      ∀ state,
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal state →
        stateMeaning state)
    (strictMeaning :
      ∀ {source child},
        (∃ control cut parentInterval childInterval,
          source = .side control cut parentInterval ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span) →
        stateMeaning child →
        stateMeaning source)
    (registeredMeaning :
      ∀ edge :
          FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId QClass,
        edge ∈ edges →
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal edge.child →
        stateMeaning (.side edge.control edge.cut edge.parent))
    {source terminal}
    (path :
      NormalizedFiniteResponsePath attachment edges source terminal)
    (terminalFact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal) :
    stateMeaning source := by
  induction path with
  | refl state =>
      exact terminalMeaning state terminalFact
  | strict head tail ih =>
      exact strictMeaning head (ih terminalFact)
  | registered edge member =>
      exact registeredMeaning edge member terminalFact

theorem selectedSide_realize_of_normalized_path_meaning
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {soa : SOAInstance β}
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    {roots : List (InitialSideRoot Ctl Cut)}
    (hchecked : responseTableNonSideChildrenB edges = true)
    (stateMeaning :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (terminalMeaning :
      ∀ state,
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal state →
        stateMeaning state)
    (strictMeaning :
      ∀ {source child},
        (∃ control cut parentInterval childInterval,
          source = .side control cut parentInterval ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span) →
        stateMeaning child →
        stateMeaning source)
    (registeredMeaning :
      ∀ edge :
          FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId QClass,
        edge ∈ edges →
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal edge.child →
        stateMeaning (.side edge.control edge.cut edge.parent))
    (selectedSideMeaning :
      ∀ root ∈ roots,
        stateMeaning (.side root.control root.cut root.parent) →
        ∃ word : Word β, soa.Avoider word) :
    ∀ root ∈ roots,
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        (.side root.control root.cut root.parent) →
      ∃ word : Word β, soa.Avoider word := by
  apply selectedSide_realize_of_normalized_table_paths hchecked
  intro root hroot terminal path terminalFact
  apply selectedSideMeaning root hroot
  exact path.meaning stateMeaning terminalMeaning strictMeaning
    registeredMeaning terminalFact

def normalizedTableSideRootRealizationSemantics
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
    (edges :
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
    (hchecked : responseTableNonSideChildrenB edges = true)
    (stateMeaning :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (terminalMeaning :
      ∀ state,
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal state →
        stateMeaning state)
    (strictMeaning :
      ∀ {source child},
        (∃ control cutValue parentInterval childInterval,
          source = .side control cutValue parentInterval ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span) →
        stateMeaning child →
        stateMeaning source)
    (registeredMeaning :
      ∀ edge :
          FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId QClass,
        edge ∈ edges →
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal edge.child →
        stateMeaning (.side edge.control edge.cut edge.parent))
    (selectedSideMeaning :
      ∀ root ∈ roots,
        stateMeaning (.side root.control root.cut root.parent) →
        ∃ word : Word β, soa.Avoider word) :
    InitialSideRootRealizationSemantics soa
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      roots := by
  apply fullyComposedSemanticSideRootRealization
    soa summaryOf attachment I left right rightFinal event w j t
    (attachmentResponseTableEnabled edges) localTerminal
    ctl cut ori intervals macros wires loops locals quotient roots
  exact selectedSide_realize_of_normalized_path_meaning
    hchecked stateMeaning terminalMeaning strictMeaning
    registeredMeaning selectedSideMeaning

end NSSE
