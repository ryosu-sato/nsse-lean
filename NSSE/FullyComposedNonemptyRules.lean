import NSSE.AttachmentResponseDispatcher

/-!
# Every fully composed recursive rule has a child

The fully composed compiler has only unary loop and side-response rules.
Atomic bounded states are terminals and have no enabled recursive rule.
-/

namespace NSSE

universe u

theorem fullyComposed_enabled_children_ne_nil
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
    (parent :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (children :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (henabled :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
      ).enabled parent children = true) :
    children ≠ [] := by
  have harity :=
    ((fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t localEnabled localTerminal
      ).dispatchEnabled_correct parent children).1 henabled
  intro hnil
  subst children
  cases parent <;>
    simp [fullyComposedRuleTests, CompilerTagRuleTests.merge,
      finiteLoopRuleTests, attachmentResponseRuleTests,
      unifiedAtomicRuleTests, CompilerTag.kind] at harity

end NSSE
