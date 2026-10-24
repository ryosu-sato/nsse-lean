import NSSE.FullyComposedRuleSoundness

/-!
# Concrete response-tree semantics of the fully composed compiler

The compiler's terminals must not all be identified with avoiders:
nonidentity loops, finite guard failures, and local mismatch atoms express
different facts.  `FullyComposedSemantic` records those facts faithfully
and closes them under interval-side and registered-response edges.

The executable derivation is sound for this inductive semantics without
any additional assumptions.  Consequently the only remaining global
realization theorem is stated at the correct level: every selected side
root carrying such a semantic response tree realizes an avoider.
-/

namespace NSSE

universe u

inductive FullyComposedSemantic
    [DecidableEq QC] [DecidableEq QL]
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
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool) :
    FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass → Prop
  | nonidentity
      (tag) (loopId)
      (loop_id : tag.loopId? = some loopId)
      (nonidentity : ¬ IdentityLoop (summaryOf loopId)) :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal tag
  | side
      (control : Ctl) (cut : Cut) (parent : NatInterval) (child)
      (enabled :
        intervalSideEnabled attachment
          control cut parent child = true)
      (child_semantic :
        FullyComposedSemantic summaryOf attachment I left right
          rightFinal event w j t localEnabled localTerminal child) :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal
        (.side control cut parent)
  | localResponse
      (control : Ctl) (cut : Cut) (parent : NatInterval) (child)
      (enabled : localEnabled control cut parent child = true)
      (child_semantic :
        FullyComposedSemantic summaryOf attachment I left right
          rightFinal event w j t localEnabled localTerminal child) :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal
        (.side control cut parent)
  | guard
      (control : Ctl) (cut : Cut)
      (query : FirstEventFiniteGuardQuery
        I left right event w j t)
      (solved :
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true) :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal
        (.bounded control cut (.inl query))
  | local
      (control : Ctl) (cut : Cut) (localId : LocalId)
      (terminal : localTerminal localId = true) :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal
        (.bounded control cut (.inr localId))

theorem FullyComposedSemantic.nonidentity_of_loopId
    [DecidableEq QC] [DecidableEq QL]
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool}
    {localTerminal : LocalId → Bool}
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    (semantic :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal state)
    {loopId : LoopId}
    (hloop : state.loopId? = some loopId) :
    ¬ IdentityLoop (summaryOf loopId) := by
  cases semantic with
  | nonidentity tag found hfound hnonidentity =>
      rw [hloop] at hfound
      have heq := Option.some.inj hfound
      subst found
      exact hnonidentity
  | side control cut parent child henabled hchild =>
      simp [CompilerTag.loopId?] at hloop
  | localResponse control cut parent child henabled hchild =>
      simp [CompilerTag.loopId?] at hloop
  | guard control cut query hsolved =>
      simp [CompilerTag.loopId?] at hloop
  | «local» control cut localId hterminal =>
      simp [CompilerTag.loopId?] at hloop

theorem fullyComposedSemantic_ruleTests_sound
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
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool) :
    CompilerTagRuleTests.SemanticallySound
      (fullyComposedRuleTests summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal)
      (FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal) :=
  fullyComposedRuleTests_semanticallySound
    summaryOf attachment I left right rightFinal event w j t
    localEnabled localTerminal _
    (fun tag loopId hloop hnonidentity =>
      .nonidentity tag loopId hloop hnonidentity)
    (fun control cut parent child henabled hchild =>
      .side control cut parent child henabled hchild)
    (fun control cut parent child henabled hchild =>
      .localResponse control cut parent child henabled hchild)
    (fun control cut query hsolved =>
      .guard control cut query hsolved)
    (fun control cut localId hterminal =>
      .local control cut localId hterminal)

theorem FullyComposedSemantic.taggedDerives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool}
    {localTerminal : LocalId → Bool}
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    (semantic :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal state) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives state := by
  induction semantic with
  | nonidentity tag loopId hloop hnonidentity =>
      apply NumberedRuleSystem.TaggedDerives.terminal
      change
        (fullyComposedRuleTests summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal).dispatchTerminal tag = true
      unfold fullyComposedRuleTests
      rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
      exact Or.inl
        ((finiteLoop_dispatchTerminal_iff summaryOf tag).2
          ⟨loopId, hloop, hnonidentity⟩)
  | side control cutValue parent child henabled hchild ih =>
      apply
        (fullyComposed_side_taggedDerives_iff
          summaryOf attachment I left right rightFinal event w j t
          localEnabled localTerminal ctl cut ori intervals macros wires
          loops locals quotient control cutValue parent).2
      exact ⟨child, Or.inl henabled, ih⟩
  | localResponse control cutValue parent child henabled hchild ih =>
      apply
        (fullyComposed_side_taggedDerives_iff
          summaryOf attachment I left right rightFinal event w j t
          localEnabled localTerminal ctl cut ori intervals macros wires
          loops locals quotient control cutValue parent).2
      exact ⟨child, Or.inr henabled, ih⟩
  | guard control cutValue query hsolved =>
      apply NumberedRuleSystem.TaggedDerives.terminal
      change
        (fullyComposedRuleTests summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal).dispatchTerminal
            (.bounded control cutValue (.inl query)) = true
      unfold fullyComposedRuleTests
      rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
        CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
      exact Or.inr (Or.inr (by
        simpa [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] using hsolved))
  | «local» control cutValue localId hterminal =>
      apply NumberedRuleSystem.TaggedDerives.terminal
      change
        (fullyComposedRuleTests summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal).dispatchTerminal
            (.bounded control cutValue (.inr localId)) = true
      unfold fullyComposedRuleTests
      rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
        CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
      exact Or.inr (Or.inr (by
        simpa [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal] using hterminal))

theorem fullyComposed_taggedDerives_semantic
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
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    (derive :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        ).TaggedDerives state) :
    FullyComposedSemantic summaryOf attachment I left right
      rightFinal event w j t localEnabled localTerminal state := by
  let sound :=
    fullyComposedSemantic_ruleTests_sound
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal
  exact sound.derives
    ctl cut ori intervals macros
    (FiniteLoopLabel.enumeration wires loops)
    (unifiedAtomicEnumeration
      (finiteGuardQueryEnumeration I left right event w j t) locals)
    quotient derive

theorem fullyComposed_taggedDerives_iff_semantic
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
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
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
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives state ↔
    FullyComposedSemantic summaryOf attachment I left right
      rightFinal event w j t localEnabled localTerminal state := by
  constructor
  · exact fullyComposed_taggedDerives_semantic
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal ctl cut ori intervals macros wires
      loops locals quotient
  · exact fun semantic =>
      semantic.taggedDerives
        ctl cut ori intervals macros wires loops locals quotient

theorem fullyComposed_structural_derives_transfer
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
    (oldEnabled newEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (oldTerminal newTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (tag :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass)
    (loopId : LoopId) (hloop : tag.loopId? = some loopId)
    (derive :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        oldEnabled oldTerminal
        ctl cut ori intervals macros wires loops locals quotient
        ).TaggedDerives tag) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      newEnabled newTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives tag := by
  have oldSemantic :=
    fullyComposed_taggedDerives_semantic
      summaryOf attachment I left right rightFinal event w j t
      oldEnabled oldTerminal ctl cut ori intervals macros wires loops
      locals quotient derive
  have hnonidentity :=
    oldSemantic.nonidentity_of_loopId hloop
  let newSemantic :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t newEnabled newTerminal tag :=
    .nonidentity tag loopId hloop hnonidentity
  exact newSemantic.taggedDerives
    ctl cut ori intervals macros wires loops locals quotient

def fullyComposedSemanticSideRootRealization
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
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
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (roots : List (InitialSideRoot Ctl Cut))
    (selected_sound :
      ∀ root ∈ roots,
        FullyComposedSemantic summaryOf attachment I left right
          rightFinal event w j t localEnabled localTerminal
          (.side root.control root.cut root.parent) →
        ∃ word : Word β, soa.Avoider word) :
    InitialSideRootRealizationSemantics soa
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      roots := by
  let sound :=
    fullyComposedSemantic_ruleTests_sound
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal
  exact sound.toInitialSideRootRealizationSemantics
    ctl cut ori intervals macros
    (FiniteLoopLabel.enumeration wires loops)
    (unifiedAtomicEnumeration
      (finiteGuardQueryEnumeration I left right event w j t) locals)
    quotient roots selected_sound

end NSSE
