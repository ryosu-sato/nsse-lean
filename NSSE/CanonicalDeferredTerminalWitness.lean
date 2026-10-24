import NSSE.CanonicalRankedDeferredCompiler
import NSSE.IndexedRootMaskCompilerSoundness
import NSSE.RankedIndexedMaskCompilerSoundness

/-!
# Internal terminal witnesses for the deferred canonical compiler

Every remaining zero-child terminal is an exact bounded avoider, hence it
satisfies every indexed forbidden mask without external terminal hypotheses.
-/

namespace NSSE

theorem canonicalRankedRelationalDeferred_terminalWitness
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
    (localEnabled :
      Ctl → Cut → SideRank 0 →
        FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount) →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount) →
        FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount) →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (locals : Enumeration (CanonicalRankedLocalId α bound))
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (state :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount))
        atomCount soa.indexedRootQueryEnumeration.values.length)
    (hterminal :
      (rankedRelationalDeferredRuleSystem summaryOf
        I left right rightFinal event sourceWord j t 0
        localEnabled (canonicalRankedLocalTerminal avoidTest)
        canonicalRankedDeferLocal provenance
        ctl cut orientation macros wires canonicalBoolEnumeration
        locals quotient).terminal state.1.tag = true) :
    ∃ word : Word α,
      soa.candidate word ∧
      soa.IndexedMaskForbids state.1.forbidden word := by
  change
    (rankedRelationalDeferredRuleTests summaryOf
      I left right rightFinal event sourceWord j t 0
      localEnabled (canonicalRankedLocalTerminal avoidTest)
      canonicalRankedDeferLocal provenance
      ).dispatchTerminal state.1.tag = true at hterminal
  have hdeterministic :
      (rankedDeferredRuleTests summaryOf
        I left right rightFinal event sourceWord j t 0
        localEnabled (canonicalRankedLocalTerminal avoidTest)
        canonicalRankedDeferLocal (fun tag => tag)
        ).dispatchTerminal state.1.tag = true := by
    rw [← rankedRelationalDeferred_dispatchTerminal_eq
      summaryOf I left right rightFinal event sourceWord j t 0
      localEnabled (canonicalRankedLocalTerminal avoidTest)
      canonicalRankedDeferLocal provenance (fun tag => tag)
      state.1.tag]
    exact hterminal
  obtain ⟨control, cutValue, bounded, hstate, htest⟩ :=
    (canonicalRankedDeferred_dispatchTerminal_iff
      soa avoidTest summaryOf I left right rightFinal event sourceWord
      j t bound localEnabled (fun tag => tag) state.1.tag).1
      hdeterministic
  have havoider : soa.Avoider bounded.word :=
    (avoidTest.correct bounded.word).1 htest
  exact ⟨bounded.word, havoider.1, by
    intro index _hmask hquery
    apply havoider.2
    exact (soa.rootCov_iff_exists_indexedRootQuery bounded.word).2
      ⟨index, hquery⟩⟩

theorem decideCanonicalRankedRelationalDeferred_sound
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
    (localEnabled :
      Ctl → Cut → SideRank 0 →
        FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount) →
        Bool)
    (provenance :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount) →
        FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount) →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (locals : Enumeration (CanonicalRankedLocalId α bound))
    (quotient : Enumeration (EuclideanSymbol predicateCount))
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
        Macro Wire Bool
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery
            I left right event sourceWord j t)
          (CanonicalRankedLocalId α bound))
        (EuclideanSymbol predicateCount) →
      List Nat)
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
          Macro Wire Bool
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery
              I left right event sourceWord j t)
            (CanonicalRankedLocalId α bound))
          (EuclideanSymbol predicateCount)))
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          (rankedRelationalDeferredRuleSystem summaryOf
            I left right rightFinal event sourceWord j t 0
            localEnabled (canonicalRankedLocalTerminal avoidTest)
            canonicalRankedDeferLocal provenance
            ctl cut orientation macros wires canonicalBoolEnumeration
            locals quotient)
          atomCount soa.indexedRootQueryEnumeration.values.length
          (allCanonicalForbiddenRequirement
            soa.indexedRootQueryEnumeration guardedRequired)
          labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        (rankedRelationalDeferredRuleSystem summaryOf
          I left right rightFinal event sourceWord j t 0
          localEnabled (canonicalRankedLocalTerminal avoidTest)
          canonicalRankedDeferLocal provenance
          ctl cut orientation macros wires canonicalBoolEnumeration
          locals quotient)
        atomCount soa.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          soa.indexedRootQueryEnumeration guardedRequired)
        labels index = true) :
    ∃ word : Word α, soa.Avoider word := by
  apply decideIndexedRootMaskState_sound_of_nonempty_rules
    soa
    (rankedRelationalDeferredRuleSystem summaryOf
      I left right rightFinal event sourceWord j t 0
      localEnabled (canonicalRankedLocalTerminal avoidTest)
      canonicalRankedDeferLocal provenance
      ctl cut orientation macros wires canonicalBoolEnumeration
      locals quotient)
    atomCount guardedRequired labels
  · intro state hterminal _hmasks
    exact canonicalRankedRelationalDeferred_terminalWitness
      soa avoidTest summaryOf I left right rightFinal event sourceWord
      j t bound atomCount localEnabled provenance ctl cut orientation
      macros wires locals quotient state hterminal
  · intro parent children henabled
    change
      (rankedRelationalDeferredRuleTests summaryOf
        I left right rightFinal event sourceWord j t 0
        localEnabled (canonicalRankedLocalTerminal avoidTest)
        canonicalRankedDeferLocal provenance
        ).dispatchEnabled parent children = true at henabled
    apply CompilerTagRuleTests.deferTerminalsBy_enabled_children_ne_nil
      (rankedFullyComposedRuleTests summaryOf
        I left right rightFinal event sourceWord j t 0
        localEnabled (canonicalRankedLocalTerminal avoidTest))
      (rankedTerminalDefer summaryOf I left right rightFinal
        event sourceWord j t canonicalRankedDeferLocal)
      provenance
    · intro baseParent baseChildren hbase
      exact rankedFullyComposed_enabled_children_ne_nil
        summaryOf I left right rightFinal event sourceWord j t 0
        localEnabled (canonicalRankedLocalTerminal avoidTest)
        baseParent baseChildren hbase
    · exact henabled
  · exact hindex
  · exact haccept

end NSSE
