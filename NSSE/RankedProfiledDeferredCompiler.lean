import NSSE.CanonicalRankedBoundedLongCompiler
import NSSE.RankedProfiledResponseCompiler
import NSSE.DeferredTerminalRules
import NSSE.AutomataDeferredLongContractionProgress
import NSSE.FiniteTerminalProvenance
import NSSE.CanonicalForbiddenTransitionLabels

/-!
# Deferred profiled responses with exact bounded terminals

Profiled first-event responses and nonidentity loop terminals are converted
to unary provenance obligations.  Exact bounded avoiders are the only
remaining zero-child terminals.
-/

namespace NSSE

abbrev ProfiledBoundedAtom (α : Type) (bound : Nat) :=
  Sum ProfiledFirstEventResponse (BoundedWord α bound)

def profiledBoundedAtomEnumeration
    (alphabet : Enumeration α) (bound : Nat) :
    Enumeration (ProfiledBoundedAtom α bound) :=
  profiledFirstEventResponseEnumeration.sum
    (boundedWordEnumeration alphabet bound)

def allRankedProfiledBoundedTags
    (alphabet : Enumeration α) (bound height : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass) :
    Enumeration
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass) :=
  CompilerTag.enumeration ctl cut ori (sideRankEnumeration height)
    macros (FiniteLoopLabel.enumeration wires loops)
    (profiledBoundedAtomEnumeration alphabet bound) quotient

def canonicalProfiledBoundedProvenance
    (I : SOAInstance α)
    (tags : Enumeration Tag) :
    CertifiedFiniteTerminalProvenance Tag
      (fun _ => ∃ word : Word α, I.Avoider word)
      (fun _ _ => True) :=
  CertifiedFiniteTerminalProvenance.allPairsForConstantMeaning
    tags (∃ word : Word α, I.Avoider word) (fun _ _ => True)

def allForbiddenTransitionMaskLabels
    [DecidableEq Query]
    (queries : Enumeration Query) :
    TransitionMaskLabels Tag where
  guarded := fun _ _ => []
  forbidden := fun _ _ => allCanonicalQueryIndices queries

theorem mem_allForbiddenTransitionMaskLabels
    [DecidableEq Query]
    (queries : Enumeration Query)
    (parent child : Tag) (query : Query) :
    enumerationIndex queries query ∈
      (allForbiddenTransitionMaskLabels queries
        ).forbidden parent child :=
  enumerationIndex_mem_allCanonicalQueryIndices queries query

def profiledBoundedAtomicTerminal
    {I : SOAInstance α}
    (avoidTest : ExactAvoiderTest I) :
    ProfiledBoundedAtom α bound → Bool
  | .inl response => profiledFirstEventResponseTerminal response
  | .inr bounded => boundedAvoiderTerminal avoidTest bounded

def rankedProfiledBoundedRuleTests
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool) :
    CompilerTagRuleTests Ctl Cut Ori (SideRank height) Macro
      (FiniteLoopLabel Wire LoopId)
      (ProfiledBoundedAtom α bound) QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((attachmentResponseRuleTests rankedSideEnabled localEnabled).merge
      {
        arities := fun _ => []
        terminal := fun kind tag =>
          match kind, tag with
          | .bounded, .bounded _ _ atom =>
              profiledBoundedAtomicTerminal avoidTest atom
          | _, _ => false
        enabled := fun _ _ _ => false
      })

def rankedProfiledBoundedDefer
    [DecidableEq Wire]
    (summaryOf : LoopId → LoopSummary Wire) :
    FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
      (ProfiledBoundedAtom α bound) QClass →
    Bool
  | tag =>
      match tag.loopId? with
      | some loopId => LoopUpdate.nonidentityB (summaryOf loopId)
      | none =>
          match tag with
          | .bounded _ _ (.inl _) => true
          | _ => false

theorem rankedProfiledBounded_enabled_children_ne_nil
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (parent :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
    (children :
      List
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass))
    (henabled :
      (rankedProfiledBoundedRuleTests summaryOf
        I avoidTest bound height localEnabled
        ).dispatchEnabled parent children = true) :
    children ≠ [] := by
  unfold rankedProfiledBoundedRuleTests at henabled
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff] at henabled
  rcases henabled with hloop | hresponse | hatomic
  · obtain ⟨loopId, hloopId, hidentity, hchildren⟩ :=
      (finiteLoop_dispatchEnabled_iff
        summaryOf parent children).1 hloop
    subst children
    simp
  · cases parent with
    | side control cutValue rank =>
        obtain ⟨child, hchildren, _⟩ :=
          (attachmentResponse_dispatchEnabled_iff
            rankedSideEnabled localEnabled
            control cutValue rank children).1 hresponse
        subst children
        simp
    | nonstrong =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hresponse
    | strong =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hresponse
    | hub =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hresponse
    | copy =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hresponse
    | bounded =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at hresponse
  · simp [CompilerTagRuleTests.dispatchEnabled] at hatomic

def rankedProfiledRelationalDeferredRuleTests
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool) :
    CompilerTagRuleTests Ctl Cut Ori (SideRank height) Macro
      (FiniteLoopLabel Wire LoopId)
      (ProfiledBoundedAtom α bound) QClass :=
  (rankedProfiledBoundedRuleTests summaryOf I avoidTest
    bound height localEnabled).deferTerminalsBy
      (rankedProfiledBoundedDefer summaryOf) provenance

def rankedProfiledRelationalDeferredRuleSystem
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (alphabet : Enumeration α) (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass) :=
  (rankedProfiledRelationalDeferredRuleTests summaryOf
    I avoidTest bound height localEnabled provenance).ruleSystem
      ctl cut ori (sideRankEnumeration height) macros
      (FiniteLoopLabel.enumeration wires loops)
      (profiledBoundedAtomEnumeration alphabet bound) quotient

theorem rankedProfiledRelationalDeferred_dispatchTerminal_iff
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass) :
    (rankedProfiledRelationalDeferredRuleTests summaryOf
      I avoidTest bound height localEnabled provenance
      ).dispatchTerminal state = true ↔
      ∃ control cutValue bounded,
        state = .bounded control cutValue (.inr bounded) ∧
        avoidTest.test bounded.word = true := by
  rw [rankedProfiledRelationalDeferredRuleTests,
    CompilerTagRuleTests.deferTerminalsBy_dispatchTerminal_eq_true_iff]
  cases state with
  | nonstrong =>
      simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal, CompilerTag.loopId?,
        rankedProfiledBoundedDefer]
  | strong =>
      simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal, CompilerTag.loopId?,
        rankedProfiledBoundedDefer]
  | hub =>
      simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal, CompilerTag.loopId?,
        rankedProfiledBoundedDefer]
  | copy =>
      simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal, CompilerTag.loopId?,
        rankedProfiledBoundedDefer]
  | side =>
      simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
        attachmentResponseRuleTests, CompilerTagRuleTests.merge,
        CompilerTagRuleTests.dispatchTerminal, CompilerTag.loopId?,
        rankedProfiledBoundedDefer]
  | bounded control cutValue atom =>
      cases atom with
      | inl response =>
          simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
            attachmentResponseRuleTests,
            profiledBoundedAtomicTerminal,
            CompilerTagRuleTests.merge,
            CompilerTagRuleTests.dispatchTerminal,
            CompilerTag.loopId?, rankedProfiledBoundedDefer]
      | inr bounded =>
          simp [rankedProfiledBoundedRuleTests, finiteLoopRuleTests,
            attachmentResponseRuleTests,
            profiledBoundedAtomicTerminal, boundedAvoiderTerminal,
            CompilerTagRuleTests.merge,
            CompilerTagRuleTests.dispatchTerminal,
            CompilerTag.kind, CompilerTag.loopId?,
            rankedProfiledBoundedDefer]
          constructor
          · intro htest
            exact ⟨control, cutValue, bounded,
              ⟨rfl, rfl, rfl⟩, htest⟩
          · rintro ⟨foundControl, foundCut, foundBounded,
              ⟨hcontrol, hcut, hbounded⟩, htest⟩
            subst foundControl
            subst foundCut
            subst foundBounded
            exact htest

theorem rankedProfiledRelationalDeferred_terminal_avoider
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
    (hterminal :
      (rankedProfiledRelationalDeferredRuleTests summaryOf
        I avoidTest bound height localEnabled provenance
        ).dispatchTerminal state = true) :
    ∃ word : Word α, I.Avoider word := by
  obtain ⟨_, _, bounded, _, htest⟩ :=
    (rankedProfiledRelationalDeferred_dispatchTerminal_iff
      summaryOf I avoidTest bound height localEnabled provenance
      state).1 hterminal
  exact ⟨bounded.word, (avoidTest.correct bounded.word).1 htest⟩

def canonicalProfiledRelationalDeferred_semanticallySound
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (alphabet : Enumeration α) (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass) :
    CompilerTagRuleTests.SemanticallySound
      (rankedProfiledRelationalDeferredRuleTests summaryOf
        I avoidTest bound height localEnabled
        (canonicalProfiledBoundedProvenance I
          (allRankedProfiledBoundedTags
            alphabet bound height ctl cut ori macros wires loops
            quotient)).test)
      (fun _ => ∃ word : Word α, I.Avoider word) := by
  let tags := allRankedProfiledBoundedTags
    alphabet bound height ctl cut ori macros wires loops quotient
  let provenance := canonicalProfiledBoundedProvenance I tags
  apply provenance.deferredSemanticallySound
    (rankedProfiledBoundedRuleTests summaryOf
      I avoidTest bound height localEnabled)
    (rankedProfiledBoundedDefer summaryOf)
    (fun _ => ∃ word : Word α, I.Avoider word)
    (fun _ _ => True)
  · intro state hterminal hnotDeferred
    apply rankedProfiledRelationalDeferred_terminal_avoider
      summaryOf I avoidTest bound height localEnabled
      provenance.test state
    exact
      (CompilerTagRuleTests.deferTerminalsBy_dispatchTerminal_eq_true_iff
        (rankedProfiledBoundedRuleTests summaryOf
          I avoidTest bound height localEnabled)
        (rankedProfiledBoundedDefer summaryOf)
        provenance.test state).2
        ⟨hterminal, hnotDeferred⟩
  · intro parent children henabled hchildren
    have hne :=
      rankedProfiledBounded_enabled_children_ne_nil
        summaryOf I avoidTest bound height localEnabled
        parent children henabled
    obtain ⟨child, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact hchildren child (by simp)

theorem canonicalProfiledRelationalDeferred_derives_avoider
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (alphabet : Enumeration α) (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
    (hderive :
      (rankedProfiledRelationalDeferredRuleSystem summaryOf
        I avoidTest alphabet bound height localEnabled
        (canonicalProfiledBoundedProvenance I
          (allRankedProfiledBoundedTags
            alphabet bound height ctl cut ori macros wires loops
            quotient)).test
        ctl cut ori macros wires loops quotient
        ).TaggedDerives state) :
    ∃ word : Word α, I.Avoider word := by
  apply
    (canonicalProfiledRelationalDeferred_semanticallySound
      summaryOf I avoidTest alphabet bound height localEnabled
      ctl cut ori macros wires loops quotient).derives
        ctl cut ori (sideRankEnumeration height) macros
        (FiniteLoopLabel.enumeration wires loops)
        (profiledBoundedAtomEnumeration alphabet bound) quotient
  exact hderive

theorem rankedProfiledRelationalDeferred_response_derives
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : SOAInstance α) (avoidTest : ExactAvoiderTest I)
    (alphabet : Enumeration α) (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (response : ProfiledFirstEventResponse)
    (child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
    (hterminal :
      profiledFirstEventResponseTerminal response = true)
    (hprovenance :
      provenance (.bounded control cutValue (.inl response)) child =
        true)
    (hchild :
      (rankedProfiledRelationalDeferredRuleSystem summaryOf
        I avoidTest alphabet bound height localEnabled provenance
        ctl cut ori macros wires loops quotient
        ).TaggedDerives child) :
    (rankedProfiledRelationalDeferredRuleSystem summaryOf
      I avoidTest alphabet bound height localEnabled provenance
      ctl cut ori macros wires loops quotient
      ).TaggedDerives
        (.bounded control cutValue (.inl response)) := by
  apply CompilerTagRuleTests.deferTerminalsBy_deferred_derives
    (rankedProfiledBoundedRuleTests summaryOf
      I avoidTest bound height localEnabled)
    (rankedProfiledBoundedDefer summaryOf) provenance
    ctl cut ori (sideRankEnumeration height) macros
    (FiniteLoopLabel.enumeration wires loops)
    (profiledBoundedAtomEnumeration alphabet bound) quotient
    (.bounded control cutValue (.inl response)) child
  · change
      (rankedProfiledBoundedRuleTests summaryOf
        I avoidTest bound height localEnabled
        ).dispatchTerminal
          (.bounded control cutValue (.inl response)) = true
    unfold rankedProfiledBoundedRuleTests
    rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
      CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
    exact Or.inr (Or.inr (by
      simpa [profiledBoundedAtomicTerminal,
        CompilerTagRuleTests.dispatchTerminal] using hterminal))
  · simp [rankedProfiledBoundedDefer, CompilerTag.loopId?]
  · exact hprovenance
  · exact hchild

theorem AutomataSOAInstance.exists_uniform_profiledDeferredStep
    [DecidableEq α] [DecidableEq QC]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
    (avoidTest : ExactAvoiderTest I.toSOA)
    (summaryOf : LoopId → LoopSummary Wire)
    (alphabet : Enumeration α) (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (atomCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass))
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass))
    (parent :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
        atomCount I.toSOA.indexedRootQueryEnumeration.values.length)
    (control : Ctl) (cutValue : Cut)
    (response : ProfiledFirstEventResponse)
    (hparent :
      parent.1.tag = .bounded control cutValue (.inl response))
    (hresponse :
      profiledFirstEventResponseTerminal response = true)
    (childTag :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
    (hprovenance :
      provenance parent.1.tag childTag = true)
    (emits :
      ∀ word shorter (index : Fin I.toSOA.rows.length),
        I.toSOA.LengthMinimalAvoider word →
        I.toSOA.candidate shorter →
        shorter.length < word.length →
        I.toSOA.IndexedRootQuery index shorter →
        enumerationIndex
            I.toSOA.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        (∃ shorter, ∃ index : Fin I.toSOA.rows.length,
          I.toSOA.candidate shorter ∧
          shorter.length < word.length ∧
          maskBit parent.1.forbidden
              (enumerationIndex
                I.toSOA.indexedRootQueryEnumeration index) = true ∧
          I.toSOA.IndexedRootQuery index shorter) ∨
        ∃ child :
            ValidGeneralizedState
              (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
                Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
              atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length,
          MinimalAvoiderMaskInvariant I.toSOA word child ∧
          1 ∈
            (requiredLabelledGeneralizedStateRuleSystem
              (rankedProfiledRelationalDeferredRuleSystem summaryOf
                I.toSOA avoidTest alphabet bound height
                localEnabled provenance
                ctl cut ori macros wires loops quotient)
              atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length
              requirement labels).arities ∧
          (requiredLabelledGeneralizedStateRuleSystem
            (rankedProfiledRelationalDeferredRuleSystem summaryOf
              I.toSOA avoidTest alphabet bound height
              localEnabled provenance
              ctl cut ori macros wires loops quotient)
            atomCount
            I.toSOA.indexedRootQueryEnumeration.values.length
            requirement labels).enabled parent [child] = true ∧
          remainingMaskCapacity atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length
              child.1 <
            remainingMaskCapacity atomCount
              I.toSOA.indexedRootQueryEnumeration.values.length
              parent.1 := by
  apply I.exists_uniform_markedShorterRoot_or_deferredStep
    candidateStates
    (rankedProfiledBoundedRuleTests summaryOf
      I.toSOA avoidTest bound height localEnabled)
    (rankedProfiledBoundedDefer summaryOf) provenance
    ctl cut ori (sideRankEnumeration height) macros
    (FiniteLoopLabel.enumeration wires loops)
    (profiledBoundedAtomEnumeration alphabet bound) quotient
    atomCount requirement labels parent childTag
  · rw [hparent]
    unfold rankedProfiledBoundedRuleTests
    rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
      CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
    exact Or.inr (Or.inr (by
      simpa [profiledBoundedAtomicTerminal,
        CompilerTagRuleTests.dispatchTerminal] using hresponse))
  · rw [hparent]
    simp [rankedProfiledBoundedDefer, CompilerTag.loopId?]
  · exact hprovenance
  · exact emits

theorem AutomataSOAInstance.exists_uniform_canonicalProfiledDeferredStep
    [DecidableEq α] [DecidableEq QC]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
    (avoidTest : ExactAvoiderTest I.toSOA)
    (summaryOf : LoopId → LoopSummary Wire)
    (alphabet : Enumeration α) (bound height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (parent :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
        0 I.toSOA.indexedRootQueryEnumeration.values.length)
    (control : Ctl) (cutValue : Cut)
    (response : ProfiledFirstEventResponse)
    (hparent :
      parent.1.tag = .bounded control cutValue (.inl response))
    (hresponse :
      profiledFirstEventResponseTerminal response = true) :
    let tags := allRankedProfiledBoundedTags
      alphabet bound height ctl cut ori macros wires loops quotient
    let provenance :=
      canonicalProfiledBoundedProvenance I.toSOA tags
    let labels :
        TransitionMaskLabels
          (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass) :=
      allForbiddenTransitionMaskLabels
        I.toSOA.indexedRootQueryEnumeration
    let requirement :=
      allCanonicalForbiddenRequirement
        I.toSOA.indexedRootQueryEnumeration (fun _ => [])
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        (∃ shorter, ∃ index : Fin I.toSOA.rows.length,
          I.toSOA.candidate shorter ∧
          shorter.length < word.length ∧
          maskBit parent.1.forbidden
              (enumerationIndex
                I.toSOA.indexedRootQueryEnumeration index) = true ∧
          I.toSOA.IndexedRootQuery index shorter) ∨
        ∃ child :
            ValidGeneralizedState
              (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
                Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass)
              0 I.toSOA.indexedRootQueryEnumeration.values.length,
          MinimalAvoiderMaskInvariant I.toSOA word child ∧
          1 ∈
            (requiredLabelledGeneralizedStateRuleSystem
              (rankedProfiledRelationalDeferredRuleSystem summaryOf
                I.toSOA avoidTest alphabet bound height
                localEnabled provenance.test
                ctl cut ori macros wires loops quotient)
              0 I.toSOA.indexedRootQueryEnumeration.values.length
              requirement labels).arities ∧
          (requiredLabelledGeneralizedStateRuleSystem
            (rankedProfiledRelationalDeferredRuleSystem summaryOf
              I.toSOA avoidTest alphabet bound height
              localEnabled provenance.test
              ctl cut ori macros wires loops quotient)
            0 I.toSOA.indexedRootQueryEnumeration.values.length
            requirement labels).enabled parent [child] = true ∧
          remainingMaskCapacity 0
              I.toSOA.indexedRootQueryEnumeration.values.length
              child.1 <
            remainingMaskCapacity 0
              I.toSOA.indexedRootQueryEnumeration.values.length
              parent.1 := by
  dsimp only
  let tags := allRankedProfiledBoundedTags
    alphabet bound height ctl cut ori macros wires loops quotient
  let provenance :=
    canonicalProfiledBoundedProvenance I.toSOA tags
  let labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId (ProfiledBoundedAtom α bound) QClass) :=
    allForbiddenTransitionMaskLabels
      I.toSOA.indexedRootQueryEnumeration
  apply I.exists_uniform_profiledDeferredStep
    candidateStates avoidTest summaryOf alphabet bound height
    localEnabled provenance.test ctl cut ori macros wires loops quotient
    0
    (allCanonicalForbiddenRequirement
      I.toSOA.indexedRootQueryEnumeration (fun _ => []))
    labels parent control cutValue response hparent hresponse parent.1.tag
  · exact provenance.required_test trivial
  · intro word shorter index hminimal hcandidate hshort hquery
    exact mem_allForbiddenTransitionMaskLabels
      I.toSOA.indexedRootQueryEnumeration parent.1.tag parent.1.tag index

end NSSE
