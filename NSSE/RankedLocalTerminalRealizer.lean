import NSSE.RankedIndexedMaskCompilerSoundness
import NSSE.NormalizedResponsePathRealization

/-!
# Building ranked indexed terminal realizers by terminal case

Local terminal IDs are discharged by an actual avoider witness.  The
remaining nonidentity and guard cases are exposed separately.
-/

namespace NSSE

def rankedFullyComposedIndexedTerminalRealizerOfMaskedLocal
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localTerminal : LocalId → Bool)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      List Nat)
    (nonidentityRealize :
      ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
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
          (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
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
          soa.IndexedMaskForbids state.1.forbidden word)
    (localRealize :
      ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
            QClass)
          atomCount soa.indexedRootQueryEnumeration.values.length,
        (∃ control cutValue localId,
          state.1.tag = .bounded control cutValue (.inr localId) ∧
          localTerminal localId = true) →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              soa.indexedRootQueryEnumeration guardedRequired)
            atomCount soa.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word β,
          soa.candidate word ∧
          soa.IndexedMaskForbids state.1.forbidden word) :
    RankedFullyComposedIndexedTerminalRealizer
      soa summaryOf I left right rightFinal event w j t height
      localTerminal atomCount guardedRequired where
  realize := by
    intro state fact hmasks
    let State :=
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
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
            soa.IndexedMaskForbids candidateState.1.forbidden word
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
      · intro control cutValue localId hterminal candidateState
          hstate hmasks
        apply localRealize candidateState
        · exact ⟨control, cutValue, localId, hstate, hterminal⟩
        · exact hmasks
    exact hmeaning state rfl hmasks

def rankedFullyComposedIndexedTerminalRealizer
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localTerminal : LocalId → Bool)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      List Nat)
    (nonidentityRealize :
      ∀ state :
        ValidGeneralizedState
          (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
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
          (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
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
          soa.IndexedMaskForbids state.1.forbidden word)
    (localRealize :
      ∀ localId, localTerminal localId = true →
        ∃ word : Word β, soa.Avoider word) :
    RankedFullyComposedIndexedTerminalRealizer
      soa summaryOf I left right rightFinal event w j t height
      localTerminal atomCount guardedRequired :=
  rankedFullyComposedIndexedTerminalRealizerOfMaskedLocal
    soa summaryOf I left right rightFinal event w j t height
    localTerminal atomCount guardedRequired
    nonidentityRealize guardRealize (by
      intro state hlocal hmasks
      obtain ⟨control, cutValue, localId, hstate, hterminal⟩ := hlocal
      obtain ⟨word, havoider⟩ := localRealize localId hterminal
      exact ⟨word, havoider.1, by
        intro index _ hquery
        apply havoider.2
        exact (soa.rootCov_iff_exists_indexedRootQuery word).2
          ⟨index, hquery⟩⟩)

def rankedFullyComposedIndexedTerminalRealizerOfAvoiders
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localTerminal : LocalId → Bool)
    (atomCount : Nat)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass →
      List Nat)
    (nonidentityAvoider :
      ∀ tag :
          FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
            Macro Wire LoopId
            (UnifiedAtomicId
              (FirstEventFiniteGuardQuery I left right event w j t)
              LocalId)
            QClass,
        ∀ loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        ∃ word : Word β, soa.Avoider word)
    (guardAvoider :
      ∀ (_control : Ctl) (_cutValue : Cut)
          (query :
            FirstEventFiniteGuardQuery I left right event w j t),
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true →
        ∃ word : Word β, soa.Avoider word)
    (localAvoider :
      ∀ localId : LocalId, localTerminal localId = true →
        ∃ word : Word β, soa.Avoider word) :
    RankedFullyComposedIndexedTerminalRealizer
      soa summaryOf I left right rightFinal event w j t height
      localTerminal atomCount guardedRequired :=
  rankedFullyComposedIndexedTerminalRealizer
    soa summaryOf I left right rightFinal event w j t height
    localTerminal atomCount guardedRequired
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
    localAvoider

end NSSE
