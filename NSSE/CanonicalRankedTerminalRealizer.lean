import NSSE.RankedLocalTerminalRealizer
import NSSE.CanonicalRankedBoundedLongCompiler
import NSSE.RankedTerminalAvoiderSemantics

/-!
# Terminal realizer for the canonical ranked local alphabet

Bounded-word local terminals are realized internally.  The remaining
external cases are nonidentity, guard, and mismatch terminals.
-/

namespace NSSE

def canonicalRankedTerminalAvoiderOfCases
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α) (avoidTest : ExactAvoiderTest soa)
    (summaryOf : Bool → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (bound : Nat)
    (nonidentityAvoider :
      ∀ tag :
          FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
            Macro Wire Bool
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right
                event sourceWord j t)
              (CanonicalRankedLocalId α bound))
            (EuclideanSymbol predicateCount),
        ∀ loopId,
          tag.loopId? = some loopId →
          ¬ IdentityLoop (summaryOf loopId) →
          ∃ word : Word α, soa.Avoider word)
    (guardAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut)
          (query :
            FirstEventFiniteGuardQuery
              I left right event sourceWord j t),
        (finiteGuardSolver I left right rightFinal
          event sourceWord j t).decide query = true →
        ∃ word : Word α, soa.Avoider word)
    (mismatchAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut),
        ∃ word : Word α, soa.Avoider word)
    (state :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
        Macro Wire Bool
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          (CanonicalRankedLocalId α bound))
        (EuclideanSymbol predicateCount))
    (fact :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event sourceWord j t
        (canonicalRankedLocalTerminal avoidTest) state) :
    ∃ word : Word α, soa.Avoider word :=
  rankedTerminalAvoiderOfCases
    soa summaryOf I left right rightFinal event sourceWord j t
    (canonicalRankedLocalTerminal avoidTest)
    nonidentityAvoider guardAvoider (by
      intro control cutValue localId hterminal
      cases localId with
      | inl bit =>
          have hbit : bit = true := by
            simpa [canonicalRankedLocalTerminal] using hterminal
          subst bit
          exact mismatchAvoider control cutValue
      | inr bounded =>
          exact ⟨bounded.word,
            (avoidTest.correct bounded.word).1 (by
              simpa [canonicalRankedLocalTerminal,
                boundedAvoiderTerminal] using hterminal)⟩)
    state fact

def canonicalRankedIndexedTerminalRealizer
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α) (avoidTest : ExactAvoiderTest soa)
    (summaryOf : Bool → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (bound atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
        Macro Wire Bool
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event sourceWord j t)
          (CanonicalRankedLocalId α bound))
        (EuclideanSymbol predicateCount) →
      List Nat)
    (nonidentityRealize :
      ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
            Macro Wire Bool
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right
                event sourceWord j t)
              (CanonicalRankedLocalId α bound))
            (EuclideanSymbol predicateCount))
          atomCount soa.indexedRootQueryEnumeration.values.length,
        (∃ loopId,
          state.1.tag.loopId? = some loopId ∧
          ¬ IdentityLoop (summaryOf loopId)) →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration guardedRequired)
            atomCount soa.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word α,
          soa.candidate word ∧
          soa.IndexedMaskForbids state.1.forbidden word)
    (guardRealize :
      ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
            Macro Wire Bool
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right
                event sourceWord j t)
              (CanonicalRankedLocalId α bound))
            (EuclideanSymbol predicateCount))
          atomCount soa.indexedRootQueryEnumeration.values.length,
        (∃ control cutValue query,
          state.1.tag = .bounded control cutValue (.inl query) ∧
          (finiteGuardSolver I left right rightFinal
            event sourceWord j t).decide query = true) →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration guardedRequired)
            atomCount soa.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word α,
          soa.candidate word ∧
          soa.IndexedMaskForbids state.1.forbidden word)
    (mismatchRealize :
      ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
            Macro Wire Bool
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right
                event sourceWord j t)
              (CanonicalRankedLocalId α bound))
            (EuclideanSymbol predicateCount))
          atomCount soa.indexedRootQueryEnumeration.values.length,
        (∃ control cutValue bit,
          state.1.tag =
            .bounded control cutValue (.inr (.inl bit)) ∧
          bit = true) →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration guardedRequired)
            atomCount soa.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word α,
          soa.candidate word ∧
          soa.IndexedMaskForbids state.1.forbidden word) :
    RankedFullyComposedIndexedTerminalRealizer
      soa summaryOf I left right rightFinal event sourceWord j t 0
      (canonicalRankedLocalTerminal avoidTest)
      atomCount guardedRequired :=
  rankedFullyComposedIndexedTerminalRealizerOfMaskedLocal
    soa summaryOf I left right rightFinal event sourceWord j t 0
    (canonicalRankedLocalTerminal avoidTest)
    atomCount guardedRequired nonidentityRealize guardRealize (by
      intro state hlocal hmasks
      obtain ⟨control, cutValue, localId, hstate, hterminal⟩ := hlocal
      cases localId with
      | inl bit =>
          apply mismatchRealize state
          · exact ⟨control, cutValue, bit, hstate, by
              simpa [canonicalRankedLocalTerminal] using hterminal⟩
          · exact hmasks
      | inr bounded =>
          have havoider : soa.Avoider bounded.word :=
            (avoidTest.correct bounded.word).1 (by
              simpa [canonicalRankedLocalTerminal,
                boundedAvoiderTerminal] using hterminal)
          exact ⟨bounded.word, havoider.1, by
            intro index _ hquery
            apply havoider.2
            exact (soa.rootCov_iff_exists_indexedRootQuery
              bounded.word).2 ⟨index, hquery⟩⟩)

def canonicalRankedIndexedTerminalRealizerOfAvoiders
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq QC] [DecidableEq QL]
    (soa : SOAInstance α) (avoidTest : ExactAvoiderTest soa)
    (summaryOf : Bool → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (bound atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
        Macro Wire Bool
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event sourceWord j t)
          (CanonicalRankedLocalId α bound))
        (EuclideanSymbol predicateCount) →
      List Nat)
    (nonidentityAvoider :
      ∀ tag :
          FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
            Macro Wire Bool
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right
                event sourceWord j t)
              (CanonicalRankedLocalId α bound))
            (EuclideanSymbol predicateCount),
        ∀ loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        ∃ word : Word α, soa.Avoider word)
    (guardAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut)
          (query :
            FirstEventFiniteGuardQuery
              I left right event sourceWord j t),
        (finiteGuardSolver I left right rightFinal
          event sourceWord j t).decide query = true →
        ∃ word : Word α, soa.Avoider word)
    (mismatchAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut),
        ∃ word : Word α, soa.Avoider word) :
    RankedFullyComposedIndexedTerminalRealizer
      soa summaryOf I left right rightFinal event sourceWord j t 0
      (canonicalRankedLocalTerminal avoidTest)
      atomCount guardedRequired :=
  canonicalRankedIndexedTerminalRealizer
    soa avoidTest summaryOf I left right rightFinal event sourceWord j t
    bound atomCount guardedRequired
    (by
      intro state hnonidentity _hmasks
      obtain ⟨loopId, hloop, hnonidentity⟩ := hnonidentity
      obtain ⟨word, havoider⟩ :=
        nonidentityAvoider state.1.tag loopId hloop hnonidentity
      exact ⟨word, havoider.1, by
        intro index _ hquery
        apply havoider.2
        exact (soa.rootCov_iff_exists_indexedRootQuery word).2
          ⟨index, hquery⟩⟩)
    (by
      intro state hguard _hmasks
      obtain ⟨control, cutValue, query, _hstate, hsolved⟩ := hguard
      obtain ⟨word, havoider⟩ :=
        guardAvoider control cutValue query hsolved
      exact ⟨word, havoider.1, by
        intro index _ hquery
        apply havoider.2
        exact (soa.rootCov_iff_exists_indexedRootQuery word).2
          ⟨index, hquery⟩⟩)
    (by
      intro state hmismatch _hmasks
      obtain ⟨control, cutValue, bit, _hstate, hbit⟩ := hmismatch
      subst bit
      obtain ⟨word, havoider⟩ := mismatchAvoider control cutValue
      exact ⟨word, havoider.1, by
        intro index _ hquery
        apply havoider.2
        exact (soa.rootCov_iff_exists_indexedRootQuery word).2
          ⟨index, hquery⟩⟩)

end NSSE
