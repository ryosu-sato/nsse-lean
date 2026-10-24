import NSSE.FullyComposedSemanticPath
import NSSE.RegisteredAttachmentResponseTable

/-!
# Classifying a response path over a fixed finite edge table

For the actual table-backed compiler, every unary response step is either
a strict interval delegation or membership of one concrete edge in the
fixed finite response list.  The strict branch records the child interval
and its decreasing span.
-/

namespace NSSE

universe u

def ClassifiedFiniteResponseEdge
    (attachment : AttachmentDomains)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass) :
    Prop :=
  (∃ control cut parentInterval childInterval,
      parent = .side control cut parentInterval ∧
      child.interval? = some childInterval ∧
      SideDelegation parentInterval childInterval attachment ∧
      childInterval.span < parentInterval.span) ∨
  ∃ edge ∈ edges,
    parent = .side edge.control edge.cut edge.parent ∧
    child = edge.child

theorem fullyComposedResponseEdge_table_classified
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (attachment : AttachmentDomains)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass)
    (hedge :
      fullyComposedResponseEdge attachment
        (attachmentResponseTableEnabled edges)
        parent child) :
    ClassifiedFiniteResponseEdge attachment edges parent child := by
  obtain ⟨control, cut, parentInterval, rfl, hresponse⟩ := hedge
  rcases hresponse with hside | hregistered
  · obtain ⟨childInterval, hinterval, hdelegate, hspan⟩ :=
      intervalSideEnabled_has_smaller_interval
        attachment control cut parentInterval child hside
    exact Or.inl
      ⟨control, cut, parentInterval, childInterval,
        rfl, hinterval, hdelegate, hspan⟩
  · have hmem :=
      (attachmentResponseTableEnabled_eq_true_iff
        edges control cut parentInterval child).1 hregistered
    let edge :
        FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass :=
      {
        control := control
        cut := cut
        parent := parentInterval
        child := child
      }
    exact Or.inr
      ⟨edge, by simpa [edge] using hmem, rfl, rfl⟩

theorem UnaryResponsePath.classify_finite_table
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (attachment : AttachmentDomains)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    {source target :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (path :
      UnaryResponsePath
        (fullyComposedResponseEdge attachment
          (attachmentResponseTableEnabled edges))
        source target) :
    UnaryResponsePath
      (ClassifiedFiniteResponseEdge attachment edges)
      source target :=
  path.map_edge fun parent child hedge =>
    fullyComposedResponseEdge_table_classified
      attachment edges parent child hedge

theorem selectedSide_realize_of_classified_table_paths
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {soa : SOAInstance β}
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    {roots : List (InitialSideRoot Ctl Cut)}
    (realizeClassifiedPath :
      ∀ root ∈ roots, ∀ terminal,
        UnaryResponsePath
          (ClassifiedFiniteResponseEdge attachment edges)
          (.side root.control root.cut root.parent) terminal →
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal terminal →
        ∃ word : Word β, soa.Avoider word) :
    ∀ root ∈ roots,
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        (.side root.control root.cut root.parent) →
      ∃ word : Word β, soa.Avoider word := by
  intro root hroot semantic
  obtain ⟨terminal, hpath, hterminal⟩ :=
    semantic.exists_terminal_path
  exact realizeClassifiedPath root hroot terminal
    (hpath.classify_finite_table attachment edges)
    hterminal

end NSSE
