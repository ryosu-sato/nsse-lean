import NSSE.NormalizedResponseForbiddenLabels

/-!
# Exact finite registries of canonical forbidden responses

A registry contains both an executable list of query labels for each edge
and the semantic relation it represents.  Soundness and completeness make
membership equivalent to that relation, so the normalized table classifier
does not omit or invent canonical query types.
-/

namespace NSSE

universe u v

structure CanonicalForbiddenResponseRegistry
    (Edge : Type u) (Query : Type v) where
  queries : Enumeration Query
  queriesOf : Edge → List Query
  Meaning : Edge → Query → Prop
  sound :
    ∀ edge query, query ∈ queriesOf edge → Meaning edge query
  complete :
    ∀ edge query, Meaning edge query → query ∈ queriesOf edge

namespace CanonicalForbiddenResponseRegistry

theorem mem_queriesOf_iff
    (registry : CanonicalForbiddenResponseRegistry Edge Query)
    (edge : Edge) (query : Query) :
    query ∈ registry.queriesOf edge ↔
      registry.Meaning edge query :=
  ⟨registry.sound edge query, registry.complete edge query⟩

theorem mem_normalizedClassifier_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (registry :
      CanonicalForbiddenResponseRegistry
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass)
        Query)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass)
    (query : Query) :
    query ∈
        normalizedResponseTableForbiddenQueries
          edges registry.queriesOf parent child ↔
      ∃ edge ∈ nonSideResponseEdges edges,
        parent = .side edge.control edge.cut edge.parent ∧
        child = edge.child ∧
        registry.Meaning edge query := by
  rw [normalizedResponseTableForbiddenQueries,
    mem_responseTableForbiddenQueries_iff]
  constructor
  · rintro ⟨edge, hedge, hparent, hchild, hquery⟩
    exact ⟨edge, hedge, hparent, hchild,
      (registry.mem_queriesOf_iff edge query).1 hquery⟩
  · rintro ⟨edge, hedge, hparent, hchild, hmeaning⟩
    exact ⟨edge, hedge, hparent, hchild,
      (registry.mem_queriesOf_iff edge query).2 hmeaning⟩

theorem normalizedClassifier_sound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (registry :
      CanonicalForbiddenResponseRegistry
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass)
        Query)
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass)
    (query : Query)
    (hquery :
      query ∈
        normalizedResponseTableForbiddenQueries
          edges registry.queriesOf parent child) :
    ∃ edge ∈ nonSideResponseEdges edges,
      parent = .side edge.control edge.cut edge.parent ∧
      child = edge.child ∧
      registry.Meaning edge query :=
  (registry.mem_normalizedClassifier_iff
    edges parent child query).1 hquery

theorem normalizedClassifier_complete
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (registry :
      CanonicalForbiddenResponseRegistry
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass)
        Query)
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)
    (hedge : edge ∈ nonSideResponseEdges edges)
    (query : Query)
    (hmeaning : registry.Meaning edge query) :
    query ∈
      normalizedResponseTableForbiddenQueries
        edges registry.queriesOf
        (.side edge.control edge.cut edge.parent) edge.child := by
  apply (registry.mem_normalizedClassifier_iff
    edges (.side edge.control edge.cut edge.parent)
      edge.child query).2
  exact ⟨edge, hedge, rfl, rfl, hmeaning⟩

end CanonicalForbiddenResponseRegistry

end NSSE
