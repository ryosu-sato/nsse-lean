import NSSE.RankedDeferredCompiler
import NSSE.CanonicalRankedBoundedLongCompiler

/-!
# Canonical provenance policy

Mismatch atoms are deferred; exact bounded-word atoms remain the only
zero-child terminals.
-/

namespace NSSE

def canonicalRankedDeferLocal :
    CanonicalRankedLocalId α bound → Bool
  | .inl _ => true
  | .inr _ => false

theorem canonicalRankedDeferred_dispatchTerminal_iff
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
    (bound : Nat)
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
    (childOf :
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
        (EuclideanSymbol predicateCount))
    (state :
      FiniteLoopCompilerTag Ctl Cut Orientation (SideRank 0)
        Macro Wire Bool
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery
            I left right event sourceWord j t)
          (CanonicalRankedLocalId α bound))
        (EuclideanSymbol predicateCount)) :
    (rankedDeferredRuleTests summaryOf I left right rightFinal
      event sourceWord j t 0 localEnabled
      (canonicalRankedLocalTerminal avoidTest)
      canonicalRankedDeferLocal childOf
      ).dispatchTerminal state = true ↔
      ∃ control cutValue bounded,
        state = .bounded control cutValue (.inr (.inr bounded)) ∧
        avoidTest.test bounded.word = true := by
  rw [rankedDeferred_dispatchTerminal_iff]
  constructor
  · rintro ⟨control, cutValue, localId, hstate,
      hterminal, hnotDeferred⟩
    cases localId with
    | inl bit =>
        simp [canonicalRankedDeferLocal] at hnotDeferred
    | inr bounded =>
        exact ⟨control, cutValue, bounded, hstate, by
          simpa [canonicalRankedLocalTerminal,
            boundedAvoiderTerminal] using hterminal⟩
  · rintro ⟨control, cutValue, bounded, hstate, hterminal⟩
    exact ⟨control, cutValue, .inr bounded, hstate,
      by
        simpa [canonicalRankedLocalTerminal,
          boundedAvoiderTerminal] using hterminal,
      by simp [canonicalRankedDeferLocal]⟩

end NSSE
