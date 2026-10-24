import NSSE.UnifiedAtomicDispatcher

/-!
# Side delegation and local response in one recursive rule family

At a side root, an attachment either descends to a proper interval child
or is discharged locally by one registered response tag.  Both are unary
recursive rules of the same `.side` constructor.
-/

namespace NSSE

universe u

def attachmentResponseRuleTests
    (sideEnabled localEnabled :
      Ctl → Cut → LCA →
        CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
          Bool) :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass where
  arities
    | .side => [1]
    | _ => []
  terminal := fun _ _ => false
  enabled := fun kind parent children =>
    match kind, parent, children with
    | .side, .side control cut parentInterval, [child] =>
        sideEnabled control cut parentInterval child ||
          localEnabled control cut parentInterval child
    | _, _, _ => false

theorem attachmentResponse_dispatchEnabled_iff
    (sideEnabled localEnabled :
      Ctl → Cut → LCA →
        CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
          Bool)
    (control : Ctl) (cut : Cut) (parent : LCA)
    (children :
      List (CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)) :
    (attachmentResponseRuleTests sideEnabled localEnabled
      ).dispatchEnabled (.side control cut parent) children = true ↔
      ∃ child,
        children = [child] ∧
        (sideEnabled control cut parent child = true ∨
          localEnabled control cut parent child = true) := by
  constructor
  · intro henabled
    have hlocal :=
      ((attachmentResponseRuleTests sideEnabled localEnabled
        ).dispatchEnabled_correct
          (.side control cut parent) children).1 henabled
    simp [attachmentResponseRuleTests, CompilerTag.kind] at hlocal
    obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp hlocal.1
    exact ⟨child, rfl, by
      simpa [attachmentResponseRuleTests, CompilerTag.kind] using
        hlocal.2⟩
  · rintro ⟨child, rfl, hchild⟩
    simpa [CompilerTagRuleTests.dispatchEnabled,
      attachmentResponseRuleTests, CompilerTag.kind] using hchild

def fullyComposedRuleTests
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
    (localTerminal : LocalId → Bool) :
    CompilerTagRuleTests Ctl Cut Ori NatInterval Macro
      (FiniteLoopLabel Wire LoopId)
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((attachmentResponseRuleTests
      (intervalSideEnabled attachment) localEnabled).merge
      (unifiedAtomicRuleTests I left right rightFinal event w j t
        localTerminal))

def fullyComposedRuleSystem
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
    (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :=
  (fullyComposedRuleTests summaryOf attachment
    I left right rightFinal event w j t localEnabled localTerminal).ruleSystem
      ctl cut ori intervals macros
      (FiniteLoopLabel.enumeration wires loops)
      (unifiedAtomicEnumeration
        (finiteGuardQueryEnumeration I left right event w j t) locals)
      quotient

theorem fullyComposed_side_dispatchEnabled_iff
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
    (control : Ctl) (cutValue : Cut) (parent : NatInterval)
    (children : List (FiniteLoopCompilerTag Ctl Cut Ori NatInterval
      Macro Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass)) :
    (fullyComposedRuleTests summaryOf attachment I left right rightFinal
      event w j t localEnabled localTerminal
      ).dispatchEnabled (.side control cutValue parent) children = true ↔
      ∃ child,
        children = [child] ∧
        (intervalSideEnabled attachment control cutValue parent child =
            true ∨
          localEnabled control cutValue parent child = true) := by
  unfold fullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  simp only [finiteLoopRuleTests,
    CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind,
    CompilerTag.loopId?, Bool.false_and, Bool.false_or,
    unifiedAtomicRuleTests]
  simp only [List.mem_nil_iff, decide_false, Bool.false_and,
    Bool.false_or]
  simp only [Bool.false_eq_true, false_or, or_false]
  change (attachmentResponseRuleTests
    (intervalSideEnabled attachment) localEnabled
    ).dispatchEnabled (.side control cutValue parent) children = true ↔ _
  exact attachmentResponse_dispatchEnabled_iff
    (intervalSideEnabled attachment) localEnabled
      control cutValue parent children

theorem fullyComposed_side_taggedDerives_iff
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
    (control : Ctl) (cutValue : Cut) (parent : NatInterval) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives (.side control cutValue parent) ↔
      ∃ child,
        (intervalSideEnabled attachment control cutValue parent child =
            true ∨
          localEnabled control cutValue parent child = true) ∧
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t localEnabled localTerminal
          ctl cut ori intervals macros wires loops locals quotient
          ).TaggedDerives child := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal =>
        simp [fullyComposedRuleSystem,
          CompilerTagRuleTests.ruleSystem,
          fullyComposedRuleTests, finiteLoopRuleTests,
          attachmentResponseRuleTests, unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTagRuleTests.merge, CompilerTag.loopId?,
          CompilerTag.kind] at hterminal
    | @rule _ children harity henabled hchildren =>
        have hresponse :=
          (fullyComposed_side_dispatchEnabled_iff
            summaryOf attachment I left right rightFinal event w j t
            localEnabled localTerminal control cutValue parent
            children).1 henabled
        obtain ⟨child, rfl, hchild⟩ := hresponse
        exact ⟨child, hchild, hchildren child (by simp)⟩
  · rintro ⟨child, henabled, hderive⟩
    apply NumberedRuleSystem.TaggedDerives.rule (children := [child])
    · simp [fullyComposedRuleSystem,
        CompilerTagRuleTests.ruleSystem,
        CompilerTagRuleTests.allArities,
        fullyComposedRuleTests, CompilerTagRuleTests.merge,
        finiteLoopRuleTests, attachmentResponseRuleTests,
        compilerTagKindEnumeration]
    · exact
        (fullyComposed_side_dispatchEnabled_iff
          summaryOf attachment I left right rightFinal event w j t
          localEnabled localTerminal control cutValue parent [child]).2
          ⟨child, rfl, henabled⟩
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hderive

end NSSE
