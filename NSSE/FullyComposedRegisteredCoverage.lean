import NSSE.FullyComposedRegisteredResidual
import NSSE.NormalizedRegisteredEmissionCoverage

/-!
# Query coverage emitted by a registered residual

A local move in the normalized response table produces its one-edge path,
the exact transition batches, and coverage of every query registered on
that edge.
-/

namespace NSSE

universe u

theorem fullyComposedLocalMove_normalizedRegisteredCoverage
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (attachment : AttachmentDomains)
    (queries : Enumeration Query)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    {parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    (hlocal :
      FullyComposedLocalMove
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        parent child) :
    ∃ path :
        NormalizedFiniteResponsePath attachment
          (nonSideResponseEdges originalEdges) parent child,
      ∃ guardedBatches forbiddenBatches,
        NormalizedResponseEmissionBatches
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf)
            path guardedBatches forbiddenBatches ∧
          NormalizedRegisteredQueryCoverage
            queries originalEdges queriesOf path forbiddenBatches := by
  obtain ⟨path, guardedBatches, forbiddenBatches, hemissions⟩ :=
    fullyComposedLocalMove_table_exists_emissions
      attachment (nonSideResponseEdges originalEdges)
      (normalizedResponseTableFirstEventTransitionMaskLabels
        queries originalEdges queriesOf)
      hlocal
  exact ⟨path, guardedBatches, forbiddenBatches, hemissions,
    hemissions.registeredQueryCoverage
      queries originalEdges queriesOf⟩

theorem fullyComposedLocalMove_marks_registeredQueries
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    (atomCount : Nat)
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          (labelledForbiddenUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          parent.1 [child.1] = true)
    (hlocal :
      FullyComposedLocalMove
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        parent.1.tag child.1.tag) :
    ∃ edge ∈ nonSideResponseEdges originalEdges,
      parent.1.tag =
          .side edge.control edge.cut edge.parent ∧
        child.1.tag = edge.child ∧
        ∀ query ∈ queriesOf edge,
          maskBit child.1.forbidden
            (enumerationIndex queries query) = true := by
  obtain ⟨edge, hedge, hparent, hchild⟩ :=
    (fullyComposedLocalMove_table_iff
      (nonSideResponseEdges originalEdges)
      parent.1.tag child.1.tag).1 hlocal
  refine ⟨edge, hedge, hparent, hchild, ?_⟩
  intro query hquery
  apply labelledFollow_marks_forbidden
    (normalizedResponseTableFirstEventTransitionMaskLabels
      queries originalEdges queriesOf)
    parent.1 child.1 hfollow
  · rw [hparent, hchild]
    exact enumerationIndex_mem_normalizedForbiddenLabel
      queries originalEdges queriesOf edge hedge query hquery
  · rw [parent.2.2]
    exact enumerationIndex_lt queries query

theorem fullyComposedLocalMove_progress_or_alreadyCovered
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    (atomCount : Nat)
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          (labelledForbiddenUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          parent.1 [child.1] = true)
    (hlocal :
      FullyComposedLocalMove
        (attachmentResponseTableEnabled
          (nonSideResponseEdges originalEdges))
        parent.1.tag child.1.tag) :
    remainingMaskCapacity atomCount queries.values.length child.1 <
        remainingMaskCapacity atomCount queries.values.length parent.1 ∨
      ∃ edge ∈ nonSideResponseEdges originalEdges,
        parent.1.tag =
            .side edge.control edge.cut edge.parent ∧
          child.1.tag = edge.child ∧
          ∀ query ∈ queriesOf edge,
            maskBit parent.1.forbidden
              (enumerationIndex queries query) = true := by
  obtain ⟨edge, hedge, hparent, hchild⟩ :=
    (fullyComposedLocalMove_table_iff
      (nonSideResponseEdges originalEdges)
      parent.1.tag child.1.tag).1 hlocal
  by_cases hunmarked :
      ∃ query ∈ queriesOf edge,
        maskBit parent.1.forbidden
          (enumerationIndex queries query) = false
  · obtain ⟨query, hquery, hfalse⟩ := hunmarked
    left
    apply remainingCapacity_lt_of_forbidden_emission_false
      (normalizedResponseTableFirstEventTransitionMaskLabels
        queries originalEdges queriesOf)
      parent child hfollow
      (enumerationIndex queries query)
    · rw [hparent, hchild]
      exact enumerationIndex_mem_normalizedForbiddenLabel
        queries originalEdges queriesOf edge hedge query hquery
    · rw [parent.2.2]
      exact enumerationIndex_lt queries query
    · exact hfalse
  · right
    refine ⟨edge, hedge, hparent, hchild, ?_⟩
    intro query hquery
    cases hbit :
        maskBit parent.1.forbidden
          (enumerationIndex queries query) with
    | false =>
        exact False.elim
          (hunmarked ⟨query, hquery, hbit⟩)
    | true =>
        rfl

theorem fullyComposed_progress_or_self_or_registeredCovered
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (queries : Enumeration Query)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    (atomCount : Nat)
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          (labelledForbiddenUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          parent.1 [child.1] = true)
    (hcases :
      remainingMaskCapacity atomCount queries.values.length child.1 <
          remainingMaskCapacity atomCount queries.values.length parent.1 ∨
        ((parent.1.guarded = child.1.guarded ∧
            parent.1.forbidden = child.1.forbidden) ∧
          (FullyComposedIdentityMove
              summaryOf parent.1.tag child.1.tag ∨
            FullyComposedStrictMove
              attachment parent.1.tag child.1.tag ∨
            FullyComposedLocalMove
              (attachmentResponseTableEnabled
                (nonSideResponseEdges originalEdges))
              parent.1.tag child.1.tag))) :
    NatPairLexLt
        (fullyComposedProgressMeasure
          atomCount queries.values.length child.1)
        (fullyComposedProgressMeasure
          atomCount queries.values.length parent.1) ∨
      parent.1 = child.1 ∨
      ∃ edge ∈ nonSideResponseEdges originalEdges,
        parent.1.tag =
            .side edge.control edge.cut edge.parent ∧
          child.1.tag = edge.child ∧
          ∀ query ∈ queriesOf edge,
            maskBit parent.1.forbidden
              (enumerationIndex queries query) = true := by
  rcases fullyComposed_measure_or_self_or_local hcases with
      hmeasure | hself | hlocal
  · exact Or.inl hmeasure
  · exact Or.inr (Or.inl hself)
  · rcases fullyComposedLocalMove_progress_or_alreadyCovered
      queries originalEdges queriesOf atomCount
      parent child hfollow hlocal with hcapacity | hcovered
    · exact Or.inl
        (progressMeasure_lt_of_capacity_lt hcapacity)
    · exact Or.inr (Or.inr hcovered)

theorem fullyComposed_unaryMeaning_of_progress_cases
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (queries : Enumeration Query)
    (originalEdges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass →
      List Query)
    (atomCount : Nat)
    (meaning :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length →
      Prop)
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          (labelledForbiddenUpdate
            (normalizedResponseTableFirstEventTransitionMaskLabels
              queries originalEdges queriesOf))
          parent.1 [child.1] = true)
    (hcases :
      remainingMaskCapacity atomCount queries.values.length child.1 <
          remainingMaskCapacity atomCount queries.values.length parent.1 ∨
        ((parent.1.guarded = child.1.guarded ∧
            parent.1.forbidden = child.1.forbidden) ∧
          (FullyComposedIdentityMove
              summaryOf parent.1.tag child.1.tag ∨
            FullyComposedStrictMove
              attachment parent.1.tag child.1.tag ∨
            FullyComposedLocalMove
              (attachmentResponseTableEnabled
                (nonSideResponseEdges originalEdges))
              parent.1.tag child.1.tag)))
    (childMeaning : meaning child)
    (decreasingMeaning :
      NatPairLexLt
          (fullyComposedProgressMeasure
            atomCount queries.values.length child.1)
          (fullyComposedProgressMeasure
            atomCount queries.values.length parent.1) →
        meaning child →
        meaning parent)
    (registeredMeaning :
      ∀ edge ∈ nonSideResponseEdges originalEdges,
        parent.1.tag =
            .side edge.control edge.cut edge.parent →
        child.1.tag = edge.child →
        (∀ query ∈ queriesOf edge,
          maskBit parent.1.forbidden
            (enumerationIndex queries query) = true) →
        meaning child →
        meaning parent) :
    meaning parent := by
  rcases fullyComposed_progress_or_self_or_registeredCovered
      summaryOf attachment queries originalEdges queriesOf
      atomCount parent child hfollow hcases with
      hmeasure | hself | ⟨edge, hedge, hparent, hchild, hcovered⟩
  · exact decreasingMeaning hmeasure childMeaning
  · have hstate : parent = child :=
      Subtype.ext hself
    rw [hstate]
    exact childMeaning
  · exact registeredMeaning
      edge hedge hparent hchild hcovered childMeaning

end NSSE
