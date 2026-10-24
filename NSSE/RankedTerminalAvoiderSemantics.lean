import NSSE.RankedIndexedMaskCompilerSoundness
import NSSE.RankedSideRootRealizationSemantics
import NSSE.NormalizedResponsePathRealization

/-!
# Ranked realization semantics from terminal avoiders

Once every genuine terminal fact supplies an avoider, the same witness
propagates backwards through every enabled ranked rule.  The only fact
needed about recursive rules is that their child list is nonempty.
-/

namespace NSSE

theorem fullyComposedTerminalAvoider_forall_iff_exists
    [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (sourceWord : Word α)
    (j t : Nat)
    (localTerminal : LocalId → Bool)
    (hexistsTerminal :
      ∃ state :
          FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery
                I left right event sourceWord j t)
              LocalId)
            QClass,
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event sourceWord j t localTerminal state) :
    (∀ state :
        FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            LocalId)
          QClass,
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event sourceWord j t localTerminal state →
      ∃ word : Word β, soa.Avoider word) ↔
      ∃ word : Word β, soa.Avoider word := by
  constructor
  · intro realize
    obtain ⟨state, hterminal⟩ := hexistsTerminal
    exact realize state hterminal
  · rintro ⟨word, havoider⟩ state _hterminal
    exact ⟨word, havoider⟩

def rankedTerminalAvoiderOfCases
    [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (sourceWord : Word α)
    (j t : Nat)
    (localTerminal : LocalId → Bool)
    (nonidentityAvoider :
      ∀ tag :
          FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery
                I left right event sourceWord j t)
              LocalId)
            QClass,
        ∀ loopId,
          tag.loopId? = some loopId →
          ¬ IdentityLoop (summaryOf loopId) →
          ∃ word : Word β, soa.Avoider word)
    (guardAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut)
          (query :
            FirstEventFiniteGuardQuery
              I left right event sourceWord j t),
        (finiteGuardSolver I left right rightFinal
          event sourceWord j t).decide query = true →
        ∃ word : Word β, soa.Avoider word)
    (localAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut) (localId : LocalId),
        localTerminal localId = true →
        ∃ word : Word β, soa.Avoider word)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event sourceWord j t)
          LocalId)
        QClass)
    (fact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event sourceWord j t localTerminal state) :
    ∃ word : Word β, soa.Avoider word := by
  apply fact.meaning
    (fun _ => ∃ word : Word β, soa.Avoider word)
  · exact nonidentityAvoider
  · exact guardAvoider
  · exact localAvoider

def rankedInitialSideRootRealizationSemanticsOfTerminalAvoiders
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (sourceWord : Word α)
    (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (terminalAvoider :
      ∀ state :
          FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery
                I left right event sourceWord j t)
              LocalId)
            QClass,
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event sourceWord j t localTerminal state →
        ∃ word : Word β, soa.Avoider word) :
    RankedInitialSideRootRealizationSemantics soa
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        localEnabled localTerminal ctl cut ori macros wires loops
        locals quotient)
      roots where
  meaning := fun _ => ∃ word : Word β, soa.Avoider word
  terminal_sound := by
    intro state hterminal
    exact terminalAvoider state
      (rankedFullyComposed_terminal_implies_fact
        summaryOf I left right rightFinal event sourceWord j t height
        localEnabled localTerminal ctl cut ori macros wires loops
        locals quotient state hterminal)
  rule_sound := by
    intro parent children henabled hchildren
    have hne :
        children ≠ [] :=
      rankedFullyComposed_enabled_children_ne_nil
        summaryOf I left right rightFinal event sourceWord j t height
        localEnabled localTerminal parent children henabled
    obtain ⟨child, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact hchildren child (by simp)
  selected_side_sound := by
    intro _root _hroot hmeaning
    exact hmeaning

theorem RankedBoundedLongCompleteness.toCertificateOfTerminalAvoiders
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {soa : SOAInstance β}
    {summaryOf : LoopId → LoopSummary Wire}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {sourceWord : Word α}
    {j t height : Nat}
    {localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            LocalId)
          QClass →
        Bool}
    {localTerminal : LocalId → Bool}
    {ctl : Enumeration Ctl} {cut : Enumeration Cut}
    {ori : Enumeration Ori} {macros : Enumeration Macro}
    {wires : Enumeration Wire} {loops : Enumeration LoopId}
    {locals : Enumeration LocalId} {quotient : Enumeration QClass}
    {boundedRoots :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            LocalId)
          QClass)}
    {roots : List (RankedInitialSideRoot height Ctl Cut)}
    {bound : Nat}
    (complete :
      RankedBoundedLongCompleteness soa
        (rankedFullyComposedRuleSystem summaryOf
          I left right rightFinal event sourceWord j t height
          localEnabled localTerminal ctl cut ori macros wires loops
          locals quotient)
        boundedRoots (rankedInitialSideRootTags roots) bound)
    (terminalAvoider :
      ∀ state :
          FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery
                I left right event sourceWord j t)
              LocalId)
            QClass,
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event sourceWord j t localTerminal state →
        ∃ word : Word β, soa.Avoider word) :
    BoundedOrLongRootCertificate soa
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        localEnabled localTerminal ctl cut ori macros wires loops
        locals quotient)
      boundedRoots (rankedInitialSideRootTags roots) bound :=
  complete.toCertificateOfSemantics
    (rankedInitialSideRootRealizationSemanticsOfTerminalAvoiders
      soa summaryOf I left right rightFinal event sourceWord j t height
      localEnabled localTerminal ctl cut ori macros wires loops locals
      quotient roots terminalAvoider)

end NSSE
