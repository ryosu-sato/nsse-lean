import NSSE.BoundedUnifiedFiniteDispatcher
import NSSE.RegisteredAttachmentResponseTable

/-!
# Finite attachment-response dispatcher

The response table now uses bounded interval codes for both its parent
key and its child tags.  This removes the impossible
`Enumeration NatInterval` premise from the fully composed rule system.
-/

namespace NSSE

abbrev BoundedFiniteAttachmentResponseEdge
    (limit : Nat)
    (Ctl Cut Ori Macro Wire LoopId Guard LocalId QClass : Type) :=
  AttachmentResponseEdge Ctl Cut (BoundedNatInterval limit)
    (FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
      Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass)

def boundedFullyComposedRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (localEnabled :
      Ctl → Cut → BoundedNatInterval limit →
        FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool) :
    CompilerTagRuleTests Ctl Cut Ori (BoundedNatInterval limit) Macro
      (FiniteLoopLabel Wire LoopId)
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((attachmentResponseRuleTests
      (boundedIntervalSideEnabled attachment) localEnabled).merge
      (unifiedAtomicRuleTests I left right rightFinal event w j t
        localTerminal))

def boundedFullyComposedRuleSystem
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (localEnabled :
      Ctl → Cut → BoundedNatInterval limit →
        FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :=
  (boundedFullyComposedRuleTests summaryOf attachment
    I left right rightFinal event w j t limit
      localEnabled localTerminal).ruleSystem
    ctl cut ori (boundedNatIntervalEnumeration limit) macros
      (FiniteLoopLabel.enumeration wires loops)
      (unifiedAtomicEnumeration
        (finiteGuardQueryEnumeration I left right event w j t) locals)
      quotient

theorem boundedFullyComposed_side_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (localEnabled :
      Ctl → Cut → BoundedNatInterval limit →
        FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (control : Ctl) (cutValue : Cut)
    (parent : BoundedNatInterval limit)
    (children :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)) :
    (boundedFullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t limit localEnabled localTerminal
      ).dispatchEnabled (.side control cutValue parent) children = true ↔
      ∃ child,
        children = [child] ∧
        (boundedIntervalSideEnabled attachment control cutValue parent
              child = true ∨
          localEnabled control cutValue parent child = true) := by
  unfold boundedFullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  simp only [finiteLoopRuleTests,
    CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind,
    CompilerTag.loopId?, Bool.false_and, Bool.false_or,
    unifiedAtomicRuleTests, List.mem_nil_iff, decide_false,
    Bool.false_eq_true, false_or, or_false]
  exact attachmentResponse_dispatchEnabled_iff
    (boundedIntervalSideEnabled attachment) localEnabled
      control cutValue parent children

theorem boundedFullyComposed_side_taggedDerives_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (localEnabled :
      Ctl → Cut → BoundedNatInterval limit →
        FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (parent : BoundedNatInterval limit) :
    (boundedFullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t limit localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.side control cutValue parent) ↔
      ∃ child,
        (boundedIntervalSideEnabled attachment control cutValue parent
              child = true ∨
          localEnabled control cutValue parent child = true) ∧
        (boundedFullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t limit
          localEnabled localTerminal ctl cut ori macros wires loops
          locals quotient).TaggedDerives child := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal =>
        simp [boundedFullyComposedRuleSystem,
          CompilerTagRuleTests.ruleSystem,
          boundedFullyComposedRuleTests, finiteLoopRuleTests,
          attachmentResponseRuleTests, unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTagRuleTests.merge, CompilerTag.loopId?,
          CompilerTag.kind] at hterminal
    | @rule _ children harity henabled hchildren =>
        obtain ⟨child, rfl, hchild⟩ :=
          (boundedFullyComposed_side_dispatchEnabled_iff
            summaryOf attachment I left right rightFinal event w j t
            limit localEnabled localTerminal control cutValue parent
            children).1 henabled
        exact ⟨child, hchild, hchildren child (by simp)⟩
  · rintro ⟨child, henabled, hderive⟩
    apply NumberedRuleSystem.TaggedDerives.rule (children := [child])
    · simp [boundedFullyComposedRuleSystem,
        CompilerTagRuleTests.ruleSystem,
        CompilerTagRuleTests.allArities,
        boundedFullyComposedRuleTests, CompilerTagRuleTests.merge,
        finiteLoopRuleTests, attachmentResponseRuleTests,
        compilerTagKindEnumeration]
    · exact
        (boundedFullyComposed_side_dispatchEnabled_iff
          summaryOf attachment I left right rightFinal event w j t
          limit localEnabled localTerminal control cutValue parent
          [child]).2 ⟨child, rfl, henabled⟩
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hderive

theorem boundedFullyComposed_registeredResponse_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge limit Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (edge :
      BoundedFiniteAttachmentResponseEdge limit Ctl Cut Ori Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hregistered : edge ∈ edges)
    (hchild :
      (boundedFullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t limit
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros wires loops locals quotient
        ).TaggedDerives edge.child) :
    (boundedFullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t limit
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.side edge.control edge.cut edge.parent) := by
  rw [boundedFullyComposed_side_taggedDerives_iff]
  exact ⟨edge.child, Or.inr
    ((attachmentResponseTableEnabled_eq_true_iff
      edges edge.control edge.cut edge.parent edge.child).2 hregistered),
    hchild⟩

theorem boundedFullyComposed_localAtom_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t limit : Nat)
    (localEnabled :
      Ctl → Cut → BoundedNatInterval limit →
        FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval limit)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (localId : LocalId)
    (hterminal : localTerminal localId = true) :
    (boundedFullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t limit localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.bounded control cutValue (.inr localId)) := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (boundedFullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t limit localEnabled localTerminal
      ).dispatchTerminal (.bounded control cutValue (.inr localId)) = true
  unfold boundedFullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  exact Or.inr (Or.inr (by
    simpa [unifiedAtomicRuleTests,
      CompilerTagRuleTests.dispatchTerminal] using hterminal))

end NSSE
