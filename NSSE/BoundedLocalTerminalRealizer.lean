import NSSE.FullyComposedIndexedMaskCompiler
import NSSE.BoundedAvoiderAtom
import NSSE.NormalizedResponsePathRealization

/-!
# Exact realization of bounded local terminals

When local IDs are bounded words and their terminal bit is the exact avoider
test, the local terminal case already supplies the required representative.
Only nonidentity-loop and finite-guard terminals remain as external
realization obligations.
-/

namespace NSSE

universe u

def boundedLocalFullyComposedTerminalRealizer
    [DecidableEq β]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (soa : SOAInstance β)
    (avoidTest : ExactAvoiderTest soa)
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
            (BoundedWord β bound))
          QClass →
        Bool)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            (BoundedWord β bound))
          QClass →
        List Nat)
    (nonidentityRealize :
      ∀ state :
          ValidGeneralizedState
            (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
              (UnifiedAtomicId
                (FirstEventFiniteGuardQuery I left right event w j t)
                (BoundedWord β bound))
              QClass)
            atomCount soa.indexedRootQueryEnumeration.values.length,
        (∃ loopId,
          state.1.tag.loopId? = some loopId ∧
          ¬ IdentityLoop (summaryOf loopId)) →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration guardedRequired)
            atomCount soa.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word β,
          soa.candidate word ∧
          soa.IndexedMaskForbids state.1.forbidden word)
    (guardRealize :
      ∀ state :
          ValidGeneralizedState
            (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
              (UnifiedAtomicId
                (FirstEventFiniteGuardQuery I left right event w j t)
                (BoundedWord β bound))
              QClass)
            atomCount soa.indexedRootQueryEnumeration.values.length,
        (∃ control cutValue query,
          state.1.tag = .bounded control cutValue (.inl query) ∧
          (finiteGuardSolver I left right rightFinal
            event w j t).decide query = true) →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration guardedRequired)
            atomCount soa.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word β,
          soa.candidate word ∧
          soa.IndexedMaskForbids state.1.forbidden word) :
    FullyComposedIndexedTerminalRealizer
      soa summaryOf attachment I left right rightFinal event w j t
      localEnabled (boundedAvoiderTerminal avoidTest)
      atomCount guardedRequired where
  realize := by
    intro state fact hmasks
    let State :=
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            (BoundedWord β bound))
          QClass)
        atomCount soa.indexedRootQueryEnumeration.values.length
    let stateMeaning :=
      fun tag =>
        ∀ candidateState : State,
          candidateState.1.tag = tag →
          requiredMasksTerminal
              (allCanonicalForbiddenRequirement
                soa.indexedRootQueryEnumeration guardedRequired)
              atomCount soa.indexedRootQueryEnumeration.values.length
              candidateState = true →
          ∃ word : Word β,
            soa.candidate word ∧
            soa.IndexedMaskForbids
              candidateState.1.forbidden word
    have hmeaning : stateMeaning state.1.tag := by
      apply fact.meaning stateMeaning
      · intro tag loopId hloop hnonidentity candidateState hstate hmasks
        apply nonidentityRealize candidateState
        · refine ⟨loopId, ?_, hnonidentity⟩
          rw [hstate]
          exact hloop
        · exact hmasks
      · intro control cutValue query hsolved candidateState hstate hmasks
        apply guardRealize candidateState
        · exact ⟨control, cutValue, query, hstate, hsolved⟩
        · exact hmasks
      · intro control cutValue bounded hterminal candidateState
          hstate hmasks
        have havoider : soa.Avoider bounded.word :=
          (avoidTest.correct bounded.word).1 hterminal
        exact ⟨bounded.word, havoider.1, by
          intro index _ hquery
          apply havoider.2
          exact (soa.rootCov_iff_exists_indexedRootQuery
            bounded.word).2 ⟨index, hquery⟩⟩
    exact hmeaning state rfl hmasks

end NSSE
