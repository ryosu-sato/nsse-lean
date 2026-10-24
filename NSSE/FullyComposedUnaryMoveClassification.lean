import NSSE.AttachmentResponseDispatcher

/-!
# Classification of fully composed unary moves

Every enabled singleton transition is an identity loop, a strict interval
delegation, or a local/registered response.  Atomic bounded tags have no
recursive transition.
-/

namespace NSSE

universe u

def FullyComposedIdentityMove
    (summaryOf : LoopId → LoopSummary Wire)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        Atom QClass) : Prop :=
  parent = child ∧
    ∃ loopId,
      parent.loopId? = some loopId ∧
      IdentityLoop (summaryOf loopId)

def FullyComposedStrictMove
    (attachment : AttachmentDomains)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        Atom QClass) : Prop :=
  ∃ control cut parentInterval childInterval,
    parent = .side control cut parentInterval ∧
    child.interval? = some childInterval ∧
    SideDelegation parentInterval childInterval attachment ∧
    childInterval.span < parentInterval.span

def FullyComposedLocalMove
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass →
        Bool)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        Atom QClass) : Prop :=
  ∃ control cut parentInterval,
    parent = .side control cut parentInterval ∧
    localEnabled control cut parentInterval child = true

theorem fullyComposed_unary_enabled_cases
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
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass)
    (henabled :
      (fullyComposedRuleTests summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal).dispatchEnabled parent [child] =
        true) :
    FullyComposedIdentityMove summaryOf parent child ∨
      FullyComposedStrictMove attachment parent child ∨
      FullyComposedLocalMove localEnabled parent child := by
  unfold fullyComposedRuleTests at henabled
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff] at henabled
  rcases henabled with hloop | hresponse | hatomic
  · obtain ⟨loopId, hloopId, hidentity, hchildren⟩ :=
      (finiteLoop_dispatchEnabled_iff
        summaryOf parent [child]).1 hloop
    simp at hchildren
    subst child
    exact Or.inl ⟨rfl, loopId, hloopId, hidentity⟩
  · right
    cases parent with
    | nonstrong =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]
          at hresponse
    | strong =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]
          at hresponse
    | hub =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]
          at hresponse
    | copy =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]
          at hresponse
    | bounded =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]
          at hresponse
    | side control cutValue parentInterval =>
        obtain ⟨found, hchildren, hside | hlocal⟩ :=
          (attachmentResponse_dispatchEnabled_iff
            (intervalSideEnabled attachment) localEnabled
            control cutValue parentInterval [child]).1 hresponse
        simp at hchildren
        · left
          cases hchildren
          obtain ⟨childInterval, hchildInterval,
              hdelegate, hspan⟩ :=
            intervalSideEnabled_has_smaller_interval
              attachment control cutValue parentInterval child hside
          exact ⟨control, cutValue, parentInterval, childInterval,
            rfl, hchildInterval, hdelegate, hspan⟩
        · right
          cases hchildren
          exact ⟨control, cutValue, parentInterval, rfl, hlocal⟩
  · cases parent <;>
      simp [unifiedAtomicRuleTests,
        CompilerTagRuleTests.dispatchEnabled, CompilerTag.kind]
        at hatomic

end NSSE
