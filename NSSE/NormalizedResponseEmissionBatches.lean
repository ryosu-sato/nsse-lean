import NSSE.MaskEmissionSaturation
import NSSE.FiniteResponsePathNormalization
import NSSE.LabelledGeneralizedStateCompleteness

/-!
# Emission batches along a normalized response path

Normalized paths live in `Prop`, so they cannot be eliminated directly into
lists.  This propositional graph relates a path proof to the chronological
guarded and forbidden batches emitted by its tag transitions.
-/

namespace NSSE

universe u

inductive NormalizedResponseEmissionBatches
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)) :
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass} →
    NormalizedFiniteResponsePath attachment edges source terminal →
    List (List Nat) → List (List Nat) → Prop
  | refl (state) :
      NormalizedResponseEmissionBatches labels
        (.refl state) [] []
  | strict
      {source child terminal}
      (head :
        ∃ control cut parentInterval childInterval,
          source = .side control cut parentInterval ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span)
      (tail :
        NormalizedFiniteResponsePath
          attachment edges child terminal)
      {guardedBatches forbiddenBatches}
      (rest :
        NormalizedResponseEmissionBatches labels tail
          guardedBatches forbiddenBatches) :
      NormalizedResponseEmissionBatches labels
        (.strict head tail)
        (labels.guarded source child :: guardedBatches)
        (labels.forbidden source child :: forbiddenBatches)
  | registered
      (edge :
        FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          Guard LocalId QClass)
      (member : edge ∈ edges) :
      NormalizedResponseEmissionBatches labels
        (.registered edge member)
        [labels.guarded
          (.side edge.control edge.cut edge.parent) edge.child]
        [labels.forbidden
          (.side edge.control edge.cut edge.parent) edge.child]

theorem NormalizedFiniteResponsePath.exists_emissionBatches
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass))
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    (path :
      NormalizedFiniteResponsePath attachment edges source terminal) :
    ∃ guardedBatches forbiddenBatches,
      NormalizedResponseEmissionBatches labels path
        guardedBatches forbiddenBatches := by
  induction path with
  | refl state =>
      exact ⟨[], [], .refl state⟩
  | strict head tail ih =>
      obtain ⟨guardedBatches, forbiddenBatches, hemissions⟩ := ih
      exact ⟨_ :: guardedBatches, _ :: forbiddenBatches,
        .strict head tail hemissions⟩
  | registered edge member =>
      exact ⟨[_], [_], .registered edge member⟩

theorem NormalizedResponseEmissionBatches.final_lengths
    {labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)}
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    {path :
      NormalizedFiniteResponsePath attachment edges source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (_hemissions :
      NormalizedResponseEmissionBatches labels path
        guardedBatches forbiddenBatches)
    (initialGuarded initialForbidden : List Bool) :
    (markBatches guardedBatches initialGuarded).length =
        initialGuarded.length ∧
      (markBatches forbiddenBatches initialForbidden).length =
        initialForbidden.length :=
  ⟨markBatches_length guardedBatches initialGuarded,
    markBatches_length forbiddenBatches initialForbidden⟩

/--
Emission batches are the exact mask trace needed to lift a normalized
unary path into the labelled generalized-state rule system.
-/
theorem NormalizedResponseEmissionBatches.labelledLiftable
    {labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)}
    {source terminal :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass}
    {path :
      NormalizedFiniteResponsePath attachment edges source terminal}
    {guardedBatches forbiddenBatches : List (List Nat)}
    (hemissions :
      NormalizedResponseEmissionBatches labels path
        guardedBatches forbiddenBatches)
    (base :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass))
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)
        atomCount queryCount → Bool)
    (hunary : 1 ∈ base.arities)
    (hterminal : base.terminal terminal = true)
    (hstrict :
      ∀ {parent child},
        (∃ control cut parentInterval childInterval,
          parent = .side control cut parentInterval ∧
          child.interval? = some childInterval ∧
          SideDelegation parentInterval childInterval attachment ∧
          childInterval.span < parentInterval.span) →
        base.enabled parent [child] = true)
    (hregistered :
      ∀ edge :
          FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
            Guard LocalId QClass,
        edge ∈ edges →
        base.enabled
          (.side edge.control edge.cut edge.parent)
          [edge.child] = true)
    (initialGuarded initialForbidden : List Bool)
    (hguardedLength : initialGuarded.length = atomCount)
    (hforbiddenLength : initialForbidden.length = queryCount)
    (hallowed :
      terminalAllowed
        ⟨GeneralizedState.mk terminal
            (markBatches guardedBatches initialGuarded)
            (markBatches forbiddenBatches initialForbidden),
          by
            constructor
            · rw [markBatches_length, hguardedLength]
            · rw [markBatches_length, hforbiddenLength]⟩ = true) :
    ∃ derive : base.TaggedDerives source,
      LabelledLiftable base atomCount queryCount
        terminalAllowed labels derive
        initialGuarded initialForbidden := by
  induction hemissions generalizing
      initialGuarded initialForbidden with
  | refl state =>
      let derive : base.TaggedDerives state :=
        .terminal hterminal
      refine ⟨derive, ?_⟩
      exact .terminal hterminal initialGuarded initialForbidden
        (by exact ⟨hguardedLength, hforbiddenLength⟩)
        (by simpa [markBatches] using hallowed)
  | @strict parent child terminal head tail
      guardedBatches forbiddenBatches rest ih =>
      have hnextGuarded :
          (markMany (labels.guarded parent child)
            initialGuarded).length = atomCount := by
        rw [markMany_length, hguardedLength]
      have hnextForbidden :
          (markMany (labels.forbidden parent child)
            initialForbidden).length = queryCount := by
        rw [markMany_length, hforbiddenLength]
      obtain ⟨childDerive, childLift⟩ :=
        ih hterminal
          (markMany (labels.guarded parent child) initialGuarded)
          (markMany (labels.forbidden parent child) initialForbidden)
          hnextGuarded hnextForbidden
          (by simpa [markBatches] using hallowed)
      let derive : base.TaggedDerives parent :=
        .rule (children := [child]) (by simpa using hunary)
          (hstrict head)
          (by
            intro candidate hcandidate
            simp only [List.mem_singleton] at hcandidate
            subst candidate
            exact childDerive)
      refine ⟨derive, ?_⟩
      apply LabelledLiftable.rule
        (children := [child]) (by simpa using hunary)
        (hstrict head)
        (by
          intro candidate hcandidate
          simp only [List.mem_singleton] at hcandidate
          subst candidate
          exact childDerive)
        initialGuarded initialForbidden
        (by exact ⟨hguardedLength, hforbiddenLength⟩)
      intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact childLift
  | @registered edge member =>
      let childDerive : base.TaggedDerives edge.child :=
        .terminal hterminal
      have hchildValid :
          (GeneralizedState.mk edge.child
            (markMany
              (labels.guarded
                (.side edge.control edge.cut edge.parent) edge.child)
              initialGuarded)
            (markMany
              (labels.forbidden
                (.side edge.control edge.cut edge.parent) edge.child)
              initialForbidden)).Valid atomCount queryCount := by
        constructor
        · rw [markMany_length, hguardedLength]
        · rw [markMany_length, hforbiddenLength]
      have childLift :
          LabelledLiftable base atomCount queryCount terminalAllowed labels
            childDerive
            (markMany
              (labels.guarded
                (.side edge.control edge.cut edge.parent) edge.child)
              initialGuarded)
            (markMany
              (labels.forbidden
                (.side edge.control edge.cut edge.parent) edge.child)
              initialForbidden) :=
        .terminal hterminal _ _ hchildValid
          (by simpa [markBatches] using hallowed)
      let parent :
          FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
            (UnifiedAtomicId Guard LocalId) QClass :=
        .side edge.control edge.cut edge.parent
      let derive : base.TaggedDerives parent :=
        .rule (children := [edge.child]) (by simpa using hunary)
          (by simpa [parent] using hregistered edge member)
          (by
            intro candidate hcandidate
            simp only [List.mem_singleton] at hcandidate
            subst candidate
            exact childDerive)
      refine ⟨derive, ?_⟩
      apply LabelledLiftable.rule
        (children := [edge.child]) (by simpa using hunary)
        (by simpa [parent] using hregistered edge member)
        (by
          intro candidate hcandidate
          simp only [List.mem_singleton] at hcandidate
          subst candidate
          exact childDerive)
        initialGuarded initialForbidden
        (by exact ⟨hguardedLength, hforbiddenLength⟩)
      intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact childLift

end NSSE
