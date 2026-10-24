import NSSE.BoundedIntervalSideTaggedRules
import NSSE.UnifiedFiniteDispatcher

/-!
# Unified finite dispatcher with bounded interval codes

This is the finite-state counterpart of `unifiedFiniteRuleTests`.
Structural loop and bounded-query rules are unchanged.  Only the LCA
field is replaced by `BoundedNatInterval limit`; side tests decode those
finite codes to the original `NatInterval` semantics.
-/

namespace NSSE

def boundedIntervalFiniteLoopTagEnumeration
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro)
    (labels : Enumeration (FiniteLoopLabel Wire LoopId))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (limit : Nat) :
    Enumeration
      (FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
        Macro Wire LoopId Atom QClass) :=
  CompilerTag.enumeration ctl cut ori
    (boundedNatIntervalEnumeration limit) macros labels atom quotient

def boundedUnifiedFiniteRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat) :
    CompilerTagRuleTests Ctl Cut Ori (BoundedNatInterval limit) Macro
      (FiniteLoopLabel Wire LoopId)
      (FirstEventFiniteGuardQuery I left right event w j t) QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((sideOnlyRuleTests
      (boundedIntervalSideEnabled attachment)).merge
      (boundedOnlyRuleTests I left right rightFinal event w j t))

def boundedUnifiedFiniteRuleSystem
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (labels : Enumeration (FiniteLoopLabel Wire LoopId))
    (queries :
      Enumeration
        (FirstEventFiniteGuardQuery I left right event w j t))
    (quotient : Enumeration QClass)
    (limit : Nat) :=
  (boundedUnifiedFiniteRuleTests summaryOf attachment I left right
    rightFinal event w j t limit).ruleSystem
      ctl cut ori (boundedNatIntervalEnumeration limit)
        macros labels queries quotient

theorem boundedUnifiedFinite_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (parent :
      FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
        Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t) QClass)
    (children :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t) QClass)) :
    (boundedUnifiedFiniteRuleTests summaryOf attachment I left right
      rightFinal event w j t limit).dispatchEnabled parent children = true ↔
      (finiteLoopRuleTests summaryOf).dispatchEnabled
          parent children = true ∨
      (sideOnlyRuleTests
        (boundedIntervalSideEnabled attachment)
        ).dispatchEnabled parent children = true := by
  unfold boundedUnifiedFiniteRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  simp [CompilerTagRuleTests.dispatchEnabled, boundedOnlyRuleTests]

end NSSE
