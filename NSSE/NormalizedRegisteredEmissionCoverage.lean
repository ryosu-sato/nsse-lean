import NSSE.NormalizedResponseEmissionBatches
import NSSE.NormalizedResponseForbiddenLabels

/-!
# Registered response queries occur in normalized emission batches

Every canonical query attached to a registered edge occurs in the
forbidden batch assigned to that response-table transition.
-/

namespace NSSE

universe u

theorem enumerationIndex_mem_normalizedForbiddenLabel
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hedge : edge ∈ nonSideResponseEdges edges)
    (query : Query) (hquery : query ∈ queriesOf edge) :
    enumerationIndex queries query ∈
      (normalizedResponseTableFirstEventTransitionMaskLabels
        queries edges queriesOf).forbidden
        (.side edge.control edge.cut edge.parent) edge.child := by
  simp only [normalizedResponseTableFirstEventTransitionMaskLabels,
    responseTableFirstEventTransitionMaskLabels,
    canonicalFirstEventTransitionMaskLabels,
    firstEventTransitionMaskLabels,
    compilerTagTransitionMaskLabels,
    canonicalForbiddenIndices, canonicalQueryIndices, List.mem_map]
  refine ⟨query, ?_, rfl⟩
  exact mem_responseTableForbiddenQueries_of_edge
    (nonSideResponseEdges edges) queriesOf edge hedge query hquery

inductive NormalizedRegisteredQueryCoverage
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query) :
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass} →
    NormalizedFiniteResponsePath attachment
      (nonSideResponseEdges originalEdges) source terminal →
    List (List Nat) → Prop
  | refl (state) :
      NormalizedRegisteredQueryCoverage
        queries originalEdges queriesOf (.refl state) []
  | strict
      {source child terminal}
      (head :
        ∃ control cut parentInterval childInterval,
          source =
              (CompilerTag.side control cut parentInterval :
                FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire
                  LoopId
                  (UnifiedAtomicId
                    (FirstEventFiniteGuardQuery
                      I left right event w j t)
                    LocalId)
                  QClass) ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span)
      (tail :
        NormalizedFiniteResponsePath attachment
          (nonSideResponseEdges originalEdges) child terminal)
      (headBatch : List Nat)
      {tailBatches : List (List Nat)}
      (tailCoverage :
        NormalizedRegisteredQueryCoverage
          queries originalEdges queriesOf tail tailBatches) :
      NormalizedRegisteredQueryCoverage
        queries originalEdges queriesOf
        (.strict head tail) (headBatch :: tailBatches)
  | registered
      (edge :
        FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass)
      (member : edge ∈ nonSideResponseEdges originalEdges)
      (batch : List Nat)
      (covers :
        ∀ query ∈ queriesOf edge,
          enumerationIndex queries query ∈ batch) :
      NormalizedRegisteredQueryCoverage
        queries originalEdges queriesOf
        (.registered edge member) [batch]

theorem NormalizedResponseEmissionBatches.registeredQueryCoverage
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    {path :
      NormalizedFiniteResponsePath attachment
        (nonSideResponseEdges originalEdges) source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches
        (normalizedResponseTableFirstEventTransitionMaskLabels
          queries originalEdges queriesOf)
        path guardedBatches forbiddenBatches) :
    NormalizedRegisteredQueryCoverage
      queries originalEdges queriesOf path forbiddenBatches := by
  induction hemissions with
  | refl state =>
      exact .refl state
  | strict head tail rest ih =>
      exact .strict head tail _ ih
  | registered edge member =>
      apply NormalizedRegisteredQueryCoverage.registered
        edge member _
      intro query hquery
      exact enumerationIndex_mem_normalizedForbiddenLabel
        queries originalEdges queriesOf edge member query hquery

/--
Every canonical query is registered on some response edge whose forbidden
label occurs among the chronological path batches.
-/
def AllCanonicalRegisteredEmission
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (forbiddenBatches : List (List Nat)) : Prop :=
  ∀ query : Query,
    ∃ edge ∈ nonSideResponseEdges originalEdges,
      query ∈ queriesOf edge ∧
      (normalizedResponseTableFirstEventTransitionMaskLabels
        queries originalEdges queriesOf).forbidden
          (.side edge.control edge.cut edge.parent) edge.child ∈
        forbiddenBatches

/--
One complete registered edge occurs in the chronological forbidden
batches.  This finite table condition is sufficient for all canonical
queries at once.
-/
def CompleteRegisteredEmission
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (forbiddenBatches : List (List Nat)) : Prop :=
  ∃ edge ∈ nonSideResponseEdges originalEdges,
    (∀ query : Query, query ∈ queriesOf edge) ∧
    (normalizedResponseTableFirstEventTransitionMaskLabels
      queries originalEdges queriesOf).forbidden
        (.side edge.control edge.cut edge.parent) edge.child ∈
      forbiddenBatches

def allQueriesOf
    (queries : Enumeration Query) (_edge : Edge) : List Query :=
  queries.values

theorem mem_allQueriesOf
    (queries : Enumeration Query) (edge : Edge) (query : Query) :
    query ∈ allQueriesOf queries edge :=
  queries.complete query

theorem allCanonicalRegisteredEmission_of_complete
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (forbiddenBatches : List (List Nat))
    (hcomplete :
      CompleteRegisteredEmission
        queries originalEdges queriesOf forbiddenBatches) :
    AllCanonicalRegisteredEmission
      queries originalEdges queriesOf forbiddenBatches := by
  obtain ⟨edge, hedge, hall, hbatch⟩ := hcomplete
  intro query
  exact ⟨edge, hedge, hall query, hbatch⟩

theorem completeRegisteredEmission_registered
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)
    (hedge : edge ∈ nonSideResponseEdges originalEdges)
    (hcomplete : ∀ query : Query, query ∈ queriesOf edge) :
    CompleteRegisteredEmission queries originalEdges queriesOf
      [(normalizedResponseTableFirstEventTransitionMaskLabels
        queries originalEdges queriesOf).forbidden
          (.side edge.control edge.cut edge.parent) edge.child] := by
  exact ⟨edge, hedge, hcomplete, by simp⟩

theorem CompleteRegisteredEmission.prepend
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {queries : Enumeration Query}
    {originalEdges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query}
    {forbiddenBatches : List (List Nat)}
    (hcomplete :
      CompleteRegisteredEmission
        queries originalEdges queriesOf forbiddenBatches)
    (batch : List Nat) :
    CompleteRegisteredEmission
      queries originalEdges queriesOf (batch :: forbiddenBatches) := by
  obtain ⟨edge, hedge, hall, hbatch⟩ := hcomplete
  exact ⟨edge, hedge, hall, by simp [hbatch]⟩

theorem allCanonicalRequirementsCovered_of_registeredEmission
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
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    (forbiddenBatches : List (List Nat))
    (hall :
      AllCanonicalRegisteredEmission
        queries originalEdges queriesOf forbiddenBatches)
    (initialForbidden : List Bool) :
    RequirementsCovered initialForbidden forbiddenBatches
      (allCanonicalQueryIndices queries) := by
  intro index hindex
  obtain ⟨query, _, hqueryIndex⟩ :=
    (mem_canonicalQueryIndices
      queries queries.values index).1 hindex
  subst index
  right
  obtain ⟨edge, hedge, hquery, hbatch⟩ := hall query
  refine
    ⟨(normalizedResponseTableFirstEventTransitionMaskLabels
        queries originalEdges queriesOf).forbidden
        (.side edge.control edge.cut edge.parent) edge.child,
      hbatch, ?_⟩
  exact enumerationIndex_mem_normalizedForbiddenLabel
    queries originalEdges queriesOf edge hedge query hquery

end NSSE
