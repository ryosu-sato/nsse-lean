import NSSE.DeferredTerminalRules
import NSSE.RankedAttachmentResponseDispatcher

/-!
# Ranked compiler with provenance-deferred terminals

Nonidentity loops and solved guards are always deferred to unary rules.
Local terminals are deferred according to `deferLocal`; this permits the
canonical compiler to defer mismatch terminals while retaining exact
bounded-word terminals.
-/

namespace NSSE

def rankedTerminalDefer
    [DecidableEq Wire] [DecidableEq QC] [DecidableEq QL]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (deferLocal : LocalId → Bool) :
    FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass →
    Bool
  | tag =>
      match tag.loopId? with
      | some loopId =>
          LoopUpdate.nonidentityB (summaryOf loopId)
      | none =>
          match tag with
          | .bounded _ _ (.inl query) =>
              (finiteGuardSolver I left right rightFinal
                event w j t).decide query
          | .bounded _ _ (.inr localId) => deferLocal localId
          | _ => false

def rankedDeferredRuleTests
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
    (localTerminal deferLocal : LocalId → Bool)
    (childOf :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :
    CompilerTagRuleTests Ctl Cut Ori (SideRank height) Macro
      (FiniteLoopLabel Wire LoopId)
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass :=
  (rankedFullyComposedRuleTests summaryOf
    I left right rightFinal event w j t height
    localEnabled localTerminal).deferTerminals
      (rankedTerminalDefer summaryOf I left right rightFinal
        event w j t deferLocal)
      childOf

def rankedRelationalDeferredRuleTests
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
    (localTerminal deferLocal : LocalId → Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool) :
    CompilerTagRuleTests Ctl Cut Ori (SideRank height) Macro
      (FiniteLoopLabel Wire LoopId)
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass :=
  (rankedFullyComposedRuleTests summaryOf
    I left right rightFinal event w j t height
    localEnabled localTerminal).deferTerminalsBy
      (rankedTerminalDefer summaryOf I left right rightFinal
        event w j t deferLocal)
      provenance

def rankedRelationalDeferredRuleSystem
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
    (localTerminal deferLocal : LocalId → Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :=
  (rankedRelationalDeferredRuleTests summaryOf
    I left right rightFinal event w j t height localEnabled
    localTerminal deferLocal provenance).ruleSystem
      ctl cut ori (sideRankEnumeration height) macros
      (FiniteLoopLabel.enumeration wires loops)
      (unifiedAtomicEnumeration
        (finiteGuardQueryEnumeration I left right event w j t) locals)
      quotient

theorem rankedRelationalDeferred_dispatchTerminal_eq
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
    (localTerminal deferLocal : LocalId → Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (childOf :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :
    (rankedRelationalDeferredRuleTests summaryOf
      I left right rightFinal event w j t height localEnabled
      localTerminal deferLocal provenance
      ).dispatchTerminal state =
    (rankedDeferredRuleTests summaryOf
      I left right rightFinal event w j t height localEnabled
      localTerminal deferLocal childOf
      ).dispatchTerminal state := by
  rfl

theorem rankedDeferred_dispatchTerminal_iff
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
    (localTerminal deferLocal : LocalId → Bool)
    (childOf :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :
    (rankedDeferredRuleTests summaryOf
      I left right rightFinal event w j t height
      localEnabled localTerminal deferLocal childOf
      ).dispatchTerminal state = true ↔
      ∃ control cutValue localId,
        state = .bounded control cutValue (.inr localId) ∧
        localTerminal localId = true ∧
        deferLocal localId = false := by
  rw [rankedDeferredRuleTests,
    CompilerTagRuleTests.deferTerminals_dispatchTerminal_eq_true_iff]
  cases state with
  | nonstrong =>
      simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, unifiedAtomicRuleTests,
        CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal,
        CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
  | strong =>
      simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, unifiedAtomicRuleTests,
        CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal,
        CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
  | hub =>
      simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, unifiedAtomicRuleTests,
        CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal,
        CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
  | copy =>
      simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, unifiedAtomicRuleTests,
        CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal,
        CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
  | side =>
      simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, unifiedAtomicRuleTests,
        CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal,
        CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
  | bounded control cutValue atom =>
      cases atom with
      | inl query =>
          simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
            attachmentResponseRuleTests, unifiedAtomicRuleTests,
            CompilerTagRuleTests.merge,
            CompilerTagRuleTests.dispatchTerminal,
            CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
      | inr localId =>
          simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
            attachmentResponseRuleTests, unifiedAtomicRuleTests,
            CompilerTagRuleTests.merge,
            CompilerTagRuleTests.dispatchTerminal,
            CompilerTag.kind, CompilerTag.loopId?, rankedTerminalDefer]
          constructor
          · rintro ⟨hterminal, hdefer⟩
            exact ⟨control, cutValue, localId,
              ⟨rfl, rfl, rfl⟩, hterminal, hdefer⟩
          · rintro ⟨foundControl, foundCut, foundLocal,
              ⟨hcontrol, hcut, hlocal⟩, hterminal, hdefer⟩
            subst foundControl
            subst foundCut
            subst foundLocal
            exact ⟨hterminal, hdefer⟩

end NSSE
