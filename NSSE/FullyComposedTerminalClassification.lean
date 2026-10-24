import NSSE.FullyComposedSemanticPath

/-!
# Classification of fully composed Boolean terminals

Every true terminal bit in the fully composed numbered system belongs to
exactly one of the semantic terminal strata: a nonidentity loop, a solved
finite guard, or a registered local terminal.
-/

namespace NSSE

universe u

theorem fullyComposed_terminal_implies_fact
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
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (hterminal :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
      ).terminal state = true) :
    FullyComposedTerminalFact summaryOf I left right rightFinal
      event w j t localTerminal state := by
  change
    (fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal).dispatchTerminal state = true
    at hterminal
  unfold fullyComposedRuleTests at hterminal
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

end NSSE
