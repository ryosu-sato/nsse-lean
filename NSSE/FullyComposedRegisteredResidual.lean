import NSSE.FullyComposedSameRankMove
import NSSE.RegisteredAttachmentResponseTable
import NSSE.FiniteResponsePathNormalization
import NSSE.NormalizedResponseEmissionBatches

/-!
# Registered form of the nondecreasing local residual

For a finite response table, the abstract local-move case is exactly
membership of one concrete registered edge.
-/

namespace NSSE

universe u

theorem fullyComposedLocalMove_table_iff
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Guard] [DecidableEq LocalId]
    [DecidableEq QClass]
    (edges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass))
    (parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass) :
    FullyComposedLocalMove
        (attachmentResponseTableEnabled edges) parent child ↔
      ∃ edge ∈ edges,
        parent = .side edge.control edge.cut edge.parent ∧
        child = edge.child := by
  constructor
  · rintro ⟨control, cutValue, parentInterval,
      hparent, henabled⟩
    let edge :
        FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass :=
      {
        control := control
        cut := cutValue
        parent := parentInterval
        child := child
      }
    have hedge : edge ∈ edges := by
      exact
        (attachmentResponseTableEnabled_eq_true_iff
          edges control cutValue parentInterval child).1 henabled
    exact ⟨edge, hedge, hparent, rfl⟩
  · rintro ⟨edge, hedge, hparent, hchild⟩
    subst parent
    subst child
    exact ⟨edge.control, edge.cut, edge.parent, rfl,
      (attachmentResponseTableEnabled_eq_true_iff
        edges edge.control edge.cut edge.parent edge.child).2 hedge⟩

theorem fullyComposedLocalMove_table_normalizedPath
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Guard] [DecidableEq LocalId]
    [DecidableEq QClass]
    (attachment : AttachmentDomains)
    (edges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass))
    {parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (hlocal :
      FullyComposedLocalMove
        (attachmentResponseTableEnabled edges) parent child) :
    NormalizedFiniteResponsePath attachment edges parent child := by
  obtain ⟨edge, hedge, hparent, hchild⟩ :=
    (fullyComposedLocalMove_table_iff
      edges parent child).1 hlocal
  subst parent
  subst child
  exact .registered edge hedge

theorem fullyComposedLocalMove_table_exists_emissions
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Guard] [DecidableEq LocalId]
    [DecidableEq QClass]
    (attachment : AttachmentDomains)
    (edges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass))
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass))
    {parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (hlocal :
      FullyComposedLocalMove
        (attachmentResponseTableEnabled edges) parent child) :
    ∃ path :
        NormalizedFiniteResponsePath attachment edges parent child,
      ∃ guardedBatches forbiddenBatches,
        NormalizedResponseEmissionBatches labels path
          guardedBatches forbiddenBatches := by
  let path :=
    fullyComposedLocalMove_table_normalizedPath
      attachment edges hlocal
  obtain ⟨guardedBatches, forbiddenBatches, hemissions⟩ :=
    path.exists_emissionBatches labels
  exact ⟨path, guardedBatches, forbiddenBatches, hemissions⟩

theorem fullyComposed_measure_or_self_or_registered
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Ori] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Guard] [DecidableEq LocalId]
    [DecidableEq QClass]
    {atomCount queryCount : Nat}
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {edges :
      List
        (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass)}
    {parent child :
      GeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)}
    (hcases :
      remainingMaskCapacity atomCount queryCount child <
          remainingMaskCapacity atomCount queryCount parent ∨
        ((parent.guarded = child.guarded ∧
            parent.forbidden = child.forbidden) ∧
          (FullyComposedIdentityMove summaryOf parent.tag child.tag ∨
            FullyComposedStrictMove attachment parent.tag child.tag ∨
            FullyComposedLocalMove
              (attachmentResponseTableEnabled edges)
              parent.tag child.tag))) :
    NatPairLexLt
        (fullyComposedProgressMeasure atomCount queryCount child)
        (fullyComposedProgressMeasure atomCount queryCount parent) ∨
      parent = child ∨
      ∃ edge ∈ edges,
        parent.tag = .side edge.control edge.cut edge.parent ∧
        child.tag = edge.child := by
  rcases fullyComposed_measure_or_self_or_local hcases with
      hmeasure | hself | hlocal
  · exact Or.inl hmeasure
  · exact Or.inr (Or.inl hself)
  · exact Or.inr (Or.inr
      ((fullyComposedLocalMove_table_iff
        edges parent.tag child.tag).1 hlocal))

end NSSE
