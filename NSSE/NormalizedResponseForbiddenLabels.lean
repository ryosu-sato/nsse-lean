import NSSE.ResponseTableForbiddenLabels
import NSSE.FiniteResponsePathNormalization

/-!
# Forbidden labels on the normalized non-side response table

Filtering registered responses to non-side children preserves every label
attached to an edge that survives the normalization.  Hence the normalized
path semantics and the generalized-state mask compiler use the same finite
response table.
-/

namespace NSSE

universe u

def normalizedResponseTableForbiddenQueries
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass → List Query) :=
  responseTableForbiddenQueries
    (nonSideResponseEdges edges) queriesOf

theorem mem_normalizedResponseTableForbiddenQueries_of_edge
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass → List Query)
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)
    (hedge : edge ∈ edges)
    (hnonside : edge.child.kind ≠ .side)
    (query : Query) (hquery : query ∈ queriesOf edge) :
    query ∈
      normalizedResponseTableForbiddenQueries edges queriesOf
        (.side edge.control edge.cut edge.parent) edge.child := by
  apply mem_responseTableForbiddenQueries_of_edge
  · exact (mem_nonSideResponseEdges edges edge).2
      ⟨hedge, hnonside⟩
  · exact hquery

def normalizedResponseTableFirstEventTransitionMaskLabels
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
        LocalId QClass → List Query) :
    TransitionMaskLabels
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass) :=
  responseTableFirstEventTransitionMaskLabels queries
    (nonSideResponseEdges edges) queriesOf

theorem normalizedResponseForbiddenUpdate_marks_edge_query
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
    (hedge : edge ∈ edges)
    (hnonside : edge.child.kind ≠ .side)
    (query : Query) (hquery : query ∈ queriesOf edge)
    (mask : List Bool)
    (hlength : mask.length = queries.values.length) :
    maskBit
        (labelledForbiddenUpdate
          (normalizedResponseTableFirstEventTransitionMaskLabels
            queries edges queriesOf)
          (.side edge.control edge.cut edge.parent)
          edge.child mask)
        (enumerationIndex queries query) = true := by
  apply responseTableForbiddenUpdate_marks_edge_query
    queries (nonSideResponseEdges edges) queriesOf edge
  · exact (mem_nonSideResponseEdges edges edge).2
      ⟨hedge, hnonside⟩
  · exact hquery
  · exact hlength

end NSSE
