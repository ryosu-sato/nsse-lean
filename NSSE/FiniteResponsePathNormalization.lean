import NSSE.FiniteResponsePathClassification

/-!
# Normal form for tables whose registered children are not side tags

Every classified response step starts at a side tag.  Hence, if all
registered table edges target non-side tags, no further response step can
follow a registered edge.  A path then consists of zero or more strict
interval delegations followed by at most one registered response.
-/

namespace NSSE

universe u

def ResponseTableHasNonSideChildren
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)) : Prop :=
  ∀ edge ∈ edges, edge.child.kind ≠ .side

def responseTableNonSideChildrenB
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)) : Bool :=
  edges.all fun edge => decide (edge.child.kind ≠ .side)

theorem responseTableNonSideChildrenB_correct
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)) :
    responseTableNonSideChildrenB edges = true ↔
      ResponseTableHasNonSideChildren edges := by
  simp [responseTableNonSideChildrenB,
    ResponseTableHasNonSideChildren]

def nonSideResponseEdges
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)) :
    List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
      Guard LocalId QClass) :=
  edges.filter fun edge => decide (edge.child.kind ≠ .side)

@[simp] theorem mem_nonSideResponseEdges
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass) :
    edge ∈ nonSideResponseEdges edges ↔
      edge ∈ edges ∧ edge.child.kind ≠ .side := by
  simp [nonSideResponseEdges]

theorem nonSideResponseEdges_checked
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)) :
    responseTableNonSideChildrenB
      (nonSideResponseEdges edges) = true := by
  apply (responseTableNonSideChildrenB_correct _).2
  intro edge hedge
  simpa using (List.mem_filter.mp hedge).2

theorem CompilerTag.kind_ne_side_of_loopId?_eq_some
    {tag :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        Atom QClass}
    {loopId : LoopId}
    (hloop : tag.loopId? = some loopId) :
    tag.kind ≠ .side := by
  cases tag <;>
    simp [CompilerTag.loopId?, CompilerTag.kind] at hloop ⊢

theorem boundedEdge_mem_nonSideResponseEdges
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (control : Ctl) (cut : Cut) (parent : NatInterval)
    (atom : UnifiedAtomicId Guard LocalId)
    (hedge :
      ({
        control := control
        cut := cut
        parent := parent
        child := CompilerTag.bounded control cut atom
      } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass) ∈ edges) :
    ({
      control := control
      cut := cut
      parent := parent
      child := CompilerTag.bounded control cut atom
    } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
      Guard LocalId QClass) ∈ nonSideResponseEdges edges := by
  apply (mem_nonSideResponseEdges edges _).2
  exact ⟨hedge, by simp [CompilerTag.kind]⟩

theorem structuralEdge_mem_nonSideResponseEdges
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq Guard] [DecidableEq LocalId] [DecidableEq QClass]
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)
    (loopId : LoopId)
    (hloop : edge.child.loopId? = some loopId)
    (hedge : edge ∈ edges) :
    edge ∈ nonSideResponseEdges edges := by
  apply (mem_nonSideResponseEdges edges edge).2
  exact ⟨hedge,
    CompilerTag.kind_ne_side_of_loopId?_eq_some hloop⟩

theorem ClassifiedFiniteResponseEdge.parent_kind_eq_side
    {attachment : AttachmentDomains}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    {parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (hedge :
      ClassifiedFiniteResponseEdge attachment edges parent child) :
    parent.kind = .side := by
  rcases hedge with hstrict | hregistered
  · obtain ⟨control, cut, interval, childInterval,
      rfl, hchild, hdelegate, hspan⟩ := hstrict
    rfl
  · obtain ⟨edge, hedge, rfl, rfl⟩ := hregistered
    rfl

theorem UnaryResponsePath.eq_of_source_not_side
    {attachment : AttachmentDomains}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    {source target :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (hsource : source.kind ≠ .side)
    (path :
      UnaryResponsePath
        (ClassifiedFiniteResponseEdge attachment edges)
        source target) :
    source = target := by
  cases path with
  | refl state =>
      rfl
  | step head tail =>
      exact False.elim
        (hsource head.parent_kind_eq_side)

inductive NormalizedFiniteResponsePath
    (attachment : AttachmentDomains)
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)) :
    FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
      (UnifiedAtomicId Guard LocalId) QClass →
    FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
      (UnifiedAtomicId Guard LocalId) QClass → Prop
  | refl (state) :
      NormalizedFiniteResponsePath attachment edges state state
  | strict {source child terminal}
      (head :
        ∃ control cut parentInterval childInterval,
          source = .side control cut parentInterval ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span)
      (tail :
        NormalizedFiniteResponsePath
          attachment edges child terminal) :
      NormalizedFiniteResponsePath attachment edges source terminal
  | registered
      (edge :
        FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass)
      (member : edge ∈ edges) :
      NormalizedFiniteResponsePath attachment edges
        (.side edge.control edge.cut edge.parent) edge.child

theorem UnaryResponsePath.normalize_finite_table
    {attachment : AttachmentDomains}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    (hnonside : ResponseTableHasNonSideChildren edges)
    {source target :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (path :
      UnaryResponsePath
        (ClassifiedFiniteResponseEdge attachment edges)
        source target) :
    NormalizedFiniteResponsePath attachment edges source target := by
  induction path with
  | refl state =>
      exact .refl state
  | @step parent child terminal head tail ih =>
      rcases head with hstrict | hregistered
      · exact .strict hstrict ih
      · obtain ⟨edge, hedge, hparent, hchild⟩ := hregistered
        have htailEq : child = terminal :=
          tail.eq_of_source_not_side
            (by
              rw [hchild]
              exact hnonside edge hedge)
        subst terminal
        subst parent
        subst child
        exact .registered edge hedge

theorem UnaryResponsePath.normalize_checked_finite_table
    {attachment : AttachmentDomains}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass)}
    (hchecked : responseTableNonSideChildrenB edges = true)
    {source target :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (path :
      UnaryResponsePath
        (ClassifiedFiniteResponseEdge attachment edges)
        source target) :
    NormalizedFiniteResponsePath attachment edges source target :=
  path.normalize_finite_table
    ((responseTableNonSideChildrenB_correct edges).1 hchecked)

theorem selectedSide_realize_of_normalized_table_paths
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
    (hchecked : responseTableNonSideChildrenB edges = true)
    (realizeNormalizedPath :
      ∀ root ∈ roots, ∀ terminal,
        NormalizedFiniteResponsePath attachment edges
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
  have hclassified :=
    hpath.classify_finite_table attachment edges
  exact realizeNormalizedPath root hroot terminal
    (hclassified.normalize_checked_finite_table hchecked)
    hterminal

end NSSE
