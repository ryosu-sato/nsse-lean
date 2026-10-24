import NSSE.RankedSideTaggedRules
import NSSE.RegisteredAttachmentResponseTable

/-!
# Fully composed response dispatcher over finite side ranks

This is the word-independent finite compiler path.  Its LCA field is
`SideRank height`; absolute interval coordinates occur only in external
semantic realization witnesses.
-/

namespace NSSE

abbrev RankedFiniteAttachmentResponseEdge
    (height : Nat)
    (Ctl Cut Ori Macro Wire LoopId Guard LocalId QClass : Type) :=
  AttachmentResponseEdge Ctl Cut (SideRank height)
    (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
      Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass)

def rankedFullyComposedRuleTests
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
    (localTerminal : LocalId → Bool) :
    CompilerTagRuleTests Ctl Cut Ori (SideRank height) Macro
      (FiniteLoopLabel Wire LoopId)
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((attachmentResponseRuleTests
      rankedSideEnabled localEnabled).merge
      (unifiedAtomicRuleTests I left right rightFinal event w j t
        localTerminal))

def rankedFullyComposedRuleSystem
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :=
  (rankedFullyComposedRuleTests summaryOf
    I left right rightFinal event w j t height
      localEnabled localTerminal).ruleSystem
    ctl cut ori (sideRankEnumeration height) macros
      (FiniteLoopLabel.enumeration wires loops)
      (unifiedAtomicEnumeration
        (finiteGuardQueryEnumeration I left right event w j t) locals)
      quotient

theorem rankedFullyComposed_side_dispatchEnabled_iff
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
    (localTerminal : LocalId → Bool)
    (control : Ctl) (cutValue : Cut) (parent : SideRank height)
    (children :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)) :
    (rankedFullyComposedRuleTests summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ).dispatchEnabled (.side control cutValue parent) children = true ↔
      ∃ child,
        children = [child] ∧
        (rankedSideEnabled control cutValue parent child = true ∨
          localEnabled control cutValue parent child = true) := by
  unfold rankedFullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  simp only [finiteLoopRuleTests,
    CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind,
    CompilerTag.loopId?, Bool.false_and, Bool.false_or,
    unifiedAtomicRuleTests, List.mem_nil_iff, decide_false,
    Bool.false_eq_true, false_or, or_false]
  exact attachmentResponse_dispatchEnabled_iff
    rankedSideEnabled localEnabled control cutValue parent children

theorem rankedFullyComposed_side_taggedDerives_iff
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (parent : SideRank height) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.side control cutValue parent) ↔
      ∃ child,
        (rankedSideEnabled control cutValue parent child = true ∨
          localEnabled control cutValue parent child = true) ∧
        (rankedFullyComposedRuleSystem summaryOf
          I left right rightFinal event w j t height
          localEnabled localTerminal ctl cut ori macros wires loops
          locals quotient).TaggedDerives child := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal =>
        simp [rankedFullyComposedRuleSystem,
          CompilerTagRuleTests.ruleSystem,
          rankedFullyComposedRuleTests, finiteLoopRuleTests,
          attachmentResponseRuleTests, unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTagRuleTests.merge, CompilerTag.loopId?,
          CompilerTag.kind] at hterminal
    | @rule _ children harity henabled hchildren =>
        obtain ⟨child, rfl, hchild⟩ :=
          (rankedFullyComposed_side_dispatchEnabled_iff
            summaryOf I left right rightFinal event w j t height
            localEnabled localTerminal control cutValue parent
            children).1 henabled
        exact ⟨child, hchild, hchildren child (by simp)⟩
  · rintro ⟨child, henabled, hderive⟩
    apply NumberedRuleSystem.TaggedDerives.rule (children := [child])
    · simp [rankedFullyComposedRuleSystem,
        CompilerTagRuleTests.ruleSystem,
        CompilerTagRuleTests.allArities,
        rankedFullyComposedRuleTests, CompilerTagRuleTests.merge,
        finiteLoopRuleTests, attachmentResponseRuleTests,
        compilerTagKindEnumeration]
    · exact
        (rankedFullyComposed_side_dispatchEnabled_iff
          summaryOf I left right rightFinal event w j t height
          localEnabled localTerminal control cutValue parent
          [child]).2 ⟨child, rfl, henabled⟩
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hderive

theorem rankedFullyComposed_registeredResponse_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (edge :
      RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hregistered : edge ∈ edges)
    (hchild :
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros wires loops locals quotient
        ).TaggedDerives edge.child) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.side edge.control edge.cut edge.parent) := by
  rw [rankedFullyComposed_side_taggedDerives_iff]
  exact ⟨edge.child, Or.inr
    ((attachmentResponseTableEnabled_eq_true_iff
      edges edge.control edge.cut edge.parent edge.child).2 hregistered),
    hchild⟩

theorem rankedFullyComposed_localAtom_derives
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (localId : LocalId)
    (hterminal : localTerminal localId = true) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.bounded control cutValue (.inr localId)) := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (rankedFullyComposedRuleTests summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ).dispatchTerminal (.bounded control cutValue (.inr localId)) = true
  unfold rankedFullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  exact Or.inr (Or.inr (by
    simpa [unifiedAtomicRuleTests,
      CompilerTagRuleTests.dispatchTerminal] using hterminal))

theorem rankedFullyComposed_guardAtom_derives
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (query : FirstEventFiniteGuardQuery I left right event w j t)
    (hterminal :
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.bounded control cutValue (.inl query)) := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (rankedFullyComposedRuleTests summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ).dispatchTerminal (.bounded control cutValue (.inl query)) = true
  unfold rankedFullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  exact Or.inr (Or.inr (by
    simpa [unifiedAtomicRuleTests,
      CompilerTagRuleTests.dispatchTerminal] using hterminal))

theorem rankedFullyComposed_localAtom_taggedDerives_iff
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (localId : LocalId) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives (.bounded control cutValue (.inr localId)) ↔
      localTerminal localId = true := by
  unfold rankedFullyComposedRuleSystem
  rw [(rankedFullyComposedRuleTests summaryOf
    I left right rightFinal event w j t height
    localEnabled localTerminal).taggedDerives_iff_terminal_or_rule]
  simp [rankedFullyComposedRuleTests, finiteLoopRuleTests,
    attachmentResponseRuleTests, unifiedAtomicRuleTests,
    CompilerTagRuleTests.merge,
    CompilerTagRuleTests.dispatchTerminal, CompilerTag.kind,
    CompilerTag.loopId?]

theorem rankedFullyComposed_structural_derives_of_nonidentity
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
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (tag :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (loopId : LoopId) (hloop : tag.loopId? = some loopId)
    (hnonidentity : ¬ IdentityLoop (summaryOf loopId)) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives tag := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (rankedFullyComposedRuleTests summaryOf
      I left right rightFinal event w j t height localEnabled localTerminal
      ).dispatchTerminal tag = true
  unfold rankedFullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  apply Or.inl
  exact (finiteLoop_dispatchTerminal_iff summaryOf tag).2
    ⟨loopId, hloop, hnonidentity⟩

end NSSE
