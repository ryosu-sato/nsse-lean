import NSSE.UnifiedFiniteDispatcher

/-!
# A common finite atom alphabet for bounded and local terminals

The `.bounded` tag constructor is the compiler's atomic-terminal slot.
For a fixed input it carries either one of the four first-event guard
queries or a finite local-response ID.  A lookup decides the latter.
-/

namespace NSSE

universe u

abbrev UnifiedAtomicId (Guard LocalId : Type u) :=
  Sum Guard LocalId

def unifiedAtomicEnumeration
    (guards : Enumeration Guard) (locals : Enumeration LocalId) :
    Enumeration (UnifiedAtomicId Guard LocalId) :=
  guards.sum locals

def unifiedAtomicRuleTests
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localTerminal : LocalId → Bool) :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass where
  arities := fun _ => []
  terminal := fun kind tag =>
    match kind, tag with
    | .bounded, .bounded _ _ (.inl query) =>
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query
    | .bounded, .bounded _ _ (.inr localId) =>
        localTerminal localId
    | _, _ => false
  enabled := fun _ _ _ => false

def fullyUnifiedRuleTests
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
    (localTerminal : LocalId → Bool) :
    CompilerTagRuleTests Ctl Cut Ori NatInterval Macro
      (FiniteLoopLabel Wire LoopId)
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((sideOnlyRuleTests (intervalSideEnabled attachment)).merge
      (unifiedAtomicRuleTests I left right rightFinal event w j t
        localTerminal))

def fullyUnifiedRuleSystem
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
        Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :=
  (fullyUnifiedRuleTests summaryOf attachment I left right rightFinal
    event w j t localTerminal).ruleSystem
      ctl cut ori intervals macros
      (FiniteLoopLabel.enumeration wires loops)
      (unifiedAtomicEnumeration
        (finiteGuardQueryEnumeration I left right event w j t) locals)
      quotient

theorem fullyUnified_localAtom_taggedDerives_iff
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (localId : LocalId) :
    (fullyUnifiedRuleSystem summaryOf attachment I left right rightFinal
      event w j t localTerminal ctl cut ori intervals macros wires loops
      locals quotient).TaggedDerives
        (.bounded control cutValue (.inr localId)) ↔
      localTerminal localId = true := by
  unfold fullyUnifiedRuleSystem
  rw [(fullyUnifiedRuleTests summaryOf attachment I left right
    rightFinal event w j t localTerminal
    ).taggedDerives_iff_terminal_or_rule]
  simp [fullyUnifiedRuleTests, finiteLoopRuleTests,
    sideOnlyRuleTests, unifiedAtomicRuleTests,
    CompilerTagRuleTests.merge,
    CompilerTagRuleTests.dispatchTerminal, CompilerTag.kind,
    CompilerTag.loopId?]

theorem fullyUnified_guardAtom_taggedDerives_iff
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (query : FirstEventFiniteGuardQuery I left right event w j t) :
    (fullyUnifiedRuleSystem summaryOf attachment I left right rightFinal
      event w j t localTerminal ctl cut ori intervals macros wires loops
      locals quotient).TaggedDerives
        (.bounded control cutValue (.inl query)) ↔
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true := by
  unfold fullyUnifiedRuleSystem
  rw [(fullyUnifiedRuleTests summaryOf attachment I left right
    rightFinal event w j t localTerminal
    ).taggedDerives_iff_terminal_or_rule]
  simp [fullyUnifiedRuleTests, finiteLoopRuleTests,
    sideOnlyRuleTests, unifiedAtomicRuleTests,
    CompilerTagRuleTests.merge,
    CompilerTagRuleTests.dispatchTerminal, CompilerTag.kind,
    CompilerTag.loopId?]

theorem fullyUnified_structural_dispatchTerminal_iff
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
    (localTerminal : LocalId → Bool)
    (tag : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass)
    (hstructural : tag.loopId?.isSome = true) :
    (fullyUnifiedRuleTests summaryOf attachment I left right rightFinal
      event w j t localTerminal).dispatchTerminal tag = true ↔
      ∃ loopId, tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  unfold fullyUnifiedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  constructor
  · rintro (hloop | hside | hatomic)
    · exact (finiteLoop_dispatchTerminal_iff summaryOf tag).1 hloop
    · cases tag <;>
        simp [sideOnlyRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hside
    · cases tag <;>
        simp [CompilerTag.loopId?, unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] at hstructural hatomic
  · intro hloop
    exact Or.inl
      ((finiteLoop_dispatchTerminal_iff summaryOf tag).2 hloop)

theorem fullyUnified_structural_dispatchEnabled_iff
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
    (localTerminal : LocalId → Bool)
    (parent : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass)
    (children : List (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass))
    (hstructural : parent.loopId?.isSome = true) :
    (fullyUnifiedRuleTests summaryOf attachment I left right rightFinal
      event w j t localTerminal).dispatchEnabled parent children = true ↔
      (finiteLoopRuleTests summaryOf).dispatchEnabled
        parent children = true := by
  unfold fullyUnifiedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  constructor
  · rintro (hloop | hside | hatomic)
    · exact hloop
    · cases parent <;>
        simp [CompilerTag.loopId?, sideOnlyRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hstructural hside
    · cases parent <;>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchEnabled] at hatomic
  · exact Or.inl

theorem fullyUnified_structural_taggedDerives_iff
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (tag : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro
      Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass)
    (hstructural : tag.loopId?.isSome = true) :
    (fullyUnifiedRuleSystem summaryOf attachment I left right rightFinal
      event w j t localTerminal ctl cut ori intervals macros wires loops
      locals quotient).TaggedDerives tag ↔
      ∃ loopId, tag.loopId? = some loopId ∧
        ¬ IdentityLoop (summaryOf loopId) := by
  constructor
  · intro hderive
    revert hstructural
    induction hderive with
    | @terminal state hterminal =>
        intro hstructural
        exact (fullyUnified_structural_dispatchTerminal_iff
          summaryOf attachment I left right rightFinal event w j t
          localTerminal state hstructural).1 hterminal
    | @rule parent children harity henabled childDerives ih =>
        intro hstructural
        have hfinite :
            (finiteLoopRuleTests summaryOf).dispatchEnabled
              parent children = true :=
          (fullyUnified_structural_dispatchEnabled_iff
            summaryOf attachment I left right rightFinal event w j t
            localTerminal parent children hstructural).1 henabled
        obtain ⟨loopId, hloop, _, hchildren⟩ :=
          (finiteLoop_dispatchEnabled_iff
            summaryOf parent children).1 hfinite
        subst children
        exact ih parent (by simp) hstructural
  · intro hterminal
    exact NumberedRuleSystem.TaggedDerives.terminal
      ((fullyUnified_structural_dispatchTerminal_iff
        summaryOf attachment I left right rightFinal event w j t
        localTerminal tag hstructural).2 hterminal)

end NSSE
