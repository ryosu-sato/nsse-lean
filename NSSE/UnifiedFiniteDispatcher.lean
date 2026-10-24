import NSSE.BoundedTaggedHorn
import NSSE.FiniteLoopDispatcher
import NSSE.IntervalSideTaggedRules

/-!
# Unified finite dispatcher

The structural loop, interval-side, and bounded-response rule families
live on one `CompilerTag` alphabet.  The bounded test is generalized
from the historical all-`Unit` tag to arbitrary finite control fields;
its semantics still depends only on the bounded query.
-/

namespace NSSE

universe u

instance finiteGuardQueryDecidableEq :
    DecidableEq
      (FirstEventFiniteGuardQuery I left right event w j t) := by
  intro first second
  cases first <;> cases second
  all_goals first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

def boundedOnlyRuleTests
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire
      (FirstEventFiniteGuardQuery I left right event w j t) QClass' where
  arities := fun _ => []
  terminal := fun kind tag =>
    match kind, tag with
    | .bounded, .bounded _ _ query =>
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query
    | _, _ => false
  enabled := fun _ _ _ => false

def unifiedFiniteRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    CompilerTagRuleTests Ctl Cut Ori NatInterval Macro
      (FiniteLoopLabel Wire LoopId)
      (FirstEventFiniteGuardQuery I left right event w j t) QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((sideOnlyRuleTests (intervalSideEnabled attachment)).merge
      (boundedOnlyRuleTests I left right rightFinal event w j t))

theorem unifiedFinite_dispatchTerminal_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass) :
    (unifiedFiniteRuleTests summaryOf attachment I left right
      rightFinal event w j t).dispatchTerminal tag = true ↔
      (finiteLoopRuleTests summaryOf).dispatchTerminal tag = true ∨
      (boundedOnlyRuleTests I left right rightFinal
        event w j t).dispatchTerminal tag = true := by
  unfold unifiedFiniteRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  simp [CompilerTagRuleTests.dispatchTerminal, sideOnlyRuleTests]

theorem unifiedFinite_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (parent : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass)
    (children : List (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass)) :
    (unifiedFiniteRuleTests summaryOf attachment I left right
      rightFinal event w j t).dispatchEnabled parent children = true ↔
      (finiteLoopRuleTests summaryOf).dispatchEnabled
          parent children = true ∨
      (sideOnlyRuleTests (intervalSideEnabled attachment)
        ).dispatchEnabled parent children = true := by
  unfold unifiedFiniteRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  simp [CompilerTagRuleTests.dispatchEnabled,
    boundedOnlyRuleTests]

theorem unifiedFinite_structural_dispatchTerminal_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass)
    (hstructural : tag.loopId?.isSome = true) :
    (unifiedFiniteRuleTests summaryOf attachment I left right
      rightFinal event w j t).dispatchTerminal tag = true ↔
      ∃ loopId, tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  rw [unifiedFinite_dispatchTerminal_iff]
  constructor
  · rintro (hloop | hbounded)
    · exact (finiteLoop_dispatchTerminal_iff summaryOf tag).1 hloop
    · cases tag <;>
        simp [CompilerTag.loopId?, boundedOnlyRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hstructural hbounded
  · intro hloop
    exact Or.inl
      ((finiteLoop_dispatchTerminal_iff summaryOf tag).2 hloop)

theorem unifiedFinite_structural_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (parent : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass)
    (children : List (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass))
    (hstructural : parent.loopId?.isSome = true) :
    (unifiedFiniteRuleTests summaryOf attachment I left right
      rightFinal event w j t).dispatchEnabled parent children = true ↔
      (finiteLoopRuleTests summaryOf).dispatchEnabled
        parent children = true := by
  rw [unifiedFinite_dispatchEnabled_iff]
  constructor
  · rintro (hloop | hside)
    · exact hloop
    · cases parent <;>
        simp [CompilerTag.loopId?, sideOnlyRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hstructural hside
  · exact Or.inl

def unifiedFiniteRuleSystem
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
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t) QClass) :=
  (unifiedFiniteRuleTests summaryOf attachment I left right
    rightFinal event w j t).ruleSystem
      ctl cut ori intervals macros
      (FiniteLoopLabel.enumeration wires loops)
      (finiteGuardQueryEnumeration I left right event w j t)
      quotient

theorem unifiedFinite_taggedDerives_iff
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
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (quotient : Enumeration QClass)
    (parent : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass) :
    (unifiedFiniteRuleSystem summaryOf attachment I left right
      rightFinal event w j t ctl cut ori intervals macros wires loops
      quotient).TaggedDerives parent ↔
      (unifiedFiniteRuleTests summaryOf attachment I left right
        rightFinal event w j t).dispatchTerminal parent = true ∨
      ∃ children : List (FiniteLoopCompilerTag Ctl Cut Ori NatInterval
          Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t) QClass),
        children.length ∈
          ((unifiedFiniteRuleTests summaryOf attachment I left right
            rightFinal event w j t) :
            CompilerTagRuleTests Ctl Cut Ori NatInterval Macro
              (FiniteLoopLabel Wire LoopId)
              (FirstEventFiniteGuardQuery I left right event w j t)
              QClass).arities parent.kind ∧
        (unifiedFiniteRuleTests summaryOf attachment I left right
          rightFinal event w j t).enabled
            parent.kind parent children = true ∧
        ∀ child ∈ children,
          (unifiedFiniteRuleSystem summaryOf attachment I left right
            rightFinal event w j t ctl cut ori intervals macros wires
            loops quotient).TaggedDerives child := by
  exact (unifiedFiniteRuleTests summaryOf attachment I left right
    rightFinal event w j t).taggedDerives_iff_terminal_or_rule
      ctl cut ori intervals macros
      (FiniteLoopLabel.enumeration wires loops)
      (finiteGuardQueryEnumeration I left right event w j t)
      quotient parent

theorem unifiedFinite_structural_taggedDerives_iff
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
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (quotient : Enumeration QClass)
    (tag : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t) QClass)
    (hstructural : tag.loopId?.isSome = true) :
    (unifiedFiniteRuleSystem summaryOf attachment I left right
      rightFinal event w j t ctl cut ori intervals macros wires loops
      quotient).TaggedDerives tag ↔
      ∃ loopId, tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  constructor
  · intro hderive
    revert hstructural
    induction hderive with
    | @terminal state hterminal =>
        intro hstructural
        exact (unifiedFinite_structural_dispatchTerminal_iff
          summaryOf attachment I left right rightFinal event w j t
          state hstructural).1 hterminal
    | @rule parent children harity henabled childDerives ih =>
        intro hstructural
        have hfinite :
            (finiteLoopRuleTests summaryOf).dispatchEnabled
              parent children = true :=
          (unifiedFinite_structural_dispatchEnabled_iff
            summaryOf attachment I left right rightFinal event w j t
            parent children hstructural).1 henabled
        obtain ⟨loopId, hloop, _, hchildren⟩ :=
          (finiteLoop_dispatchEnabled_iff
            summaryOf parent children).1 hfinite
        subst children
        exact ih parent (by simp) hstructural
  · intro hterminal
    exact NumberedRuleSystem.TaggedDerives.terminal
      ((unifiedFinite_structural_dispatchTerminal_iff
        summaryOf attachment I left right rightFinal event w j t
        tag hstructural).2 hterminal)

end NSSE
