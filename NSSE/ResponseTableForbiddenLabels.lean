import NSSE.CanonicalForbiddenTransitionLabels
import NSSE.RegisteredAttachmentResponseTable

/-!
# Canonical forbidden labels emitted by a response table

All registered response edges with the requested parent and child tags
contribute their canonical query labels.  Taking the union over matching
edges is essential when several semantic responses share the same finite
tag pair.
-/

namespace NSSE

universe u

def responseTableForbiddenQueries
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass → List Query)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass) :
    List Query :=
  edges.flatMap fun edge =>
    if parent ==
          (.side edge.control edge.cut edge.parent :
            FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
              (UnifiedAtomicId Guard LocalId) QClass) &&
        child == edge.child
    then queriesOf edge
    else []

theorem mem_responseTableForbiddenQueries_of_edge
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
    (query : Query) (hquery : query ∈ queriesOf edge) :
    query ∈
      responseTableForbiddenQueries edges queriesOf
        (.side edge.control edge.cut edge.parent) edge.child := by
  simp only [responseTableForbiddenQueries, List.mem_flatMap]
  refine ⟨edge, hedge, ?_⟩
  simpa using hquery

theorem mem_responseTableForbiddenQueries_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass → List Query)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass)
    (query : Query) :
    query ∈
        responseTableForbiddenQueries edges queriesOf parent child ↔
      ∃ edge ∈ edges,
        parent = .side edge.control edge.cut edge.parent ∧
        child = edge.child ∧
        query ∈ queriesOf edge := by
  simp only [responseTableForbiddenQueries, List.mem_flatMap]
  constructor
  · rintro ⟨edge, hedge, hquery⟩
    split at hquery
    · rename_i hmatches
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatches
      exact ⟨edge, hedge, hmatches.1, hmatches.2, hquery⟩
    · simp at hquery
  · rintro ⟨edge, hedge, rfl, rfl, hquery⟩
    exact ⟨edge, hedge, by simpa using hquery⟩

def responseTableFirstEventTransitionMaskLabels
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
  canonicalFirstEventTransitionMaskLabels queries
    (responseTableForbiddenQueries edges queriesOf)

def responseTableGeneralizedRuleSystem
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (base :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (atomCount : Nat)
    (queries : Enumeration Query)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        List Nat)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query) :
    NumberedRuleSystem
      (ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length) :=
  requiredLabelledGeneralizedStateRuleSystem
    base atomCount queries.values.length
      (allCanonicalForbiddenRequirement queries guardedRequired)
      (responseTableFirstEventTransitionMaskLabels
        queries edges queriesOf)

theorem responseTableGeneralizedRuleSystem_derives_base
    [DecidableEq Query]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (base :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (atomCount : Nat)
    (queries : Enumeration Query)
    (guardedRequired :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        List Nat)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass))
    (queriesOf :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass → List Query)
    {state :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length}
    (derive :
      (responseTableGeneralizedRuleSystem
        base atomCount queries guardedRequired edges queriesOf
      ).TaggedDerives state) :
    base.TaggedDerives state.1.tag := by
  exact labelledGeneralizedStateRuleSystem_derives_base
    base atomCount queries.values.length
      (requiredMasksTerminal
        (allCanonicalForbiddenRequirement queries guardedRequired)
        atomCount queries.values.length)
      (responseTableFirstEventTransitionMaskLabels
        queries edges queriesOf)
      derive

theorem responseTableForbiddenUpdate_marks_edge_query
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
    (query : Query) (hquery : query ∈ queriesOf edge)
    (mask : List Bool)
    (hlength : mask.length = queries.values.length) :
    maskBit
        (labelledForbiddenUpdate
          (responseTableFirstEventTransitionMaskLabels
            queries edges queriesOf)
          (.side edge.control edge.cut edge.parent)
          edge.child mask)
        (enumerationIndex queries query) = true := by
  apply canonicalForbiddenUpdate_marks_emitted
    queries (responseTableForbiddenQueries edges queriesOf)
      (.side edge.control edge.cut edge.parent) edge.child
      query
  · exact mem_responseTableForbiddenQueries_of_edge
      edges queriesOf edge hedge query hquery
  · exact hlength

end NSSE
