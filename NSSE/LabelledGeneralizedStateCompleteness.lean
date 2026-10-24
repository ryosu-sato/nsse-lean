import NSSE.LabelledGeneralizedStateRules

/-!
# Lifting base derivations to labelled generalized states

Starting from fixed root masks, every child mask is determined by the
transition labels.  `LabelledLiftable` records exactly the remaining
condition: every terminal reached by the base derivation accepts its
resulting masks.
-/

namespace NSSE

universe u

def labelledChildState
    (labels : TransitionMaskLabels Tag)
    (parent : Tag) (guarded forbidden : List Bool)
    (child : Tag) : GeneralizedState Tag where
  tag := child
  guarded :=
    labelledGuardedUpdate labels parent child guarded
  forbidden :=
    labelledForbiddenUpdate labels parent child forbidden

theorem labelledChildState_valid
    (labels : TransitionMaskLabels Tag)
    (parent child : Tag)
    (guarded forbidden : List Bool)
    (hvalid :
      (GeneralizedState.mk parent guarded forbidden).Valid
        atomCount queryCount) :
    (labelledChildState labels parent guarded forbidden child).Valid
      atomCount queryCount := by
  constructor
  · simpa [labelledChildState, labelledGuardedUpdate,
      markMany_length] using hvalid.1
  · simpa [labelledChildState, labelledForbiddenUpdate,
      markMany_length] using hvalid.2

inductive LabelledLiftable
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (labels : TransitionMaskLabels Tag) :
    {tag : Tag} → base.TaggedDerives tag →
      List Bool → List Bool → Prop
  | terminal
      {tag : Tag}
      (hterminal : base.terminal tag = true)
      (guarded forbidden : List Bool)
      (hvalid :
        (GeneralizedState.mk tag guarded forbidden).Valid
          atomCount queryCount)
      (hallowed :
        terminalAllowed
          ⟨GeneralizedState.mk tag guarded forbidden, hvalid⟩ = true) :
      LabelledLiftable base atomCount queryCount terminalAllowed labels
        (.terminal hterminal) guarded forbidden
  | rule
      {parent : Tag} {children : List Tag}
      (harity : children.length ∈ base.arities)
      (henabled : base.enabled parent children = true)
      (hchildren :
        ∀ child ∈ children, base.TaggedDerives child)
      (guarded forbidden : List Bool)
      (hvalid :
        (GeneralizedState.mk parent guarded forbidden).Valid
          atomCount queryCount)
      (hlift :
        ∀ child (hchild : child ∈ children),
          LabelledLiftable base atomCount queryCount
            terminalAllowed labels
            (hchildren child hchild)
            (labelledGuardedUpdate labels parent child guarded)
            (labelledForbiddenUpdate labels parent child forbidden)) :
      LabelledLiftable base atomCount queryCount terminalAllowed labels
        (.rule harity henabled hchildren) guarded forbidden

theorem LabelledLiftable.toTaggedDerives
    {base : NumberedRuleSystem Tag}
    {atomCount queryCount : Nat}
    {terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool}
    {labels : TransitionMaskLabels Tag}
    {tag : Tag} {derive : base.TaggedDerives tag}
    {guarded forbidden : List Bool}
    (hlift :
      LabelledLiftable base atomCount queryCount
        terminalAllowed labels derive guarded forbidden) :
    (labelledGeneralizedStateRuleSystem
      base atomCount queryCount terminalAllowed labels
    ).TaggedDerives
      ⟨GeneralizedState.mk tag guarded forbidden,
        by
          cases hlift with
          | terminal _ _ _ hvalid _ => exact hvalid
          | rule _ _ _ _ _ hvalid _ => exact hvalid⟩ := by
  induction hlift with
  | terminal hterminal guarded forbidden hvalid hallowed =>
      apply NumberedRuleSystem.TaggedDerives.terminal
      simp [labelledGeneralizedStateRuleSystem,
        transitionGeneralizedStateRuleSystem,
        Bool.and_eq_true, hterminal, hallowed]
  | @rule parent children harity henabled hchildren
      guarded forbidden hvalid hlift ih =>
      let childState := fun child =>
        (⟨labelledChildState labels parent guarded forbidden child,
          labelledChildState_valid labels parent child
            guarded forbidden hvalid⟩ :
          ValidGeneralizedState Tag atomCount queryCount)
      let childStates := children.map childState
      apply NumberedRuleSystem.TaggedDerives.rule
        (children := childStates)
      · simpa [childStates] using harity
      · simp only [labelledGeneralizedStateRuleSystem,
          transitionGeneralizedStateRuleSystem, Bool.and_eq_true]
        constructor
        · have htags :
              childStates.map (fun child => child.1.tag) = children := by
            simp only [childStates, List.map_map]
            dsimp only [childState, labelledChildState]
            change children.map id = children
            exact List.map_id children
          calc
            base.enabled parent
                (childStates.map fun child => child.1.tag) =
              base.enabled parent children :=
                congrArg (base.enabled parent) htags
            _ = true := henabled
        · simp [allStateMasksFollow, childStates, childState,
            labelledChildState, maskEqB_correct]
      · intro child hchild
        have hmapped := (List.mem_map.mp hchild)
        obtain ⟨childTag, hchildTag, heq⟩ := hmapped
        rw [← heq]
        exact ih childTag hchildTag

theorem labelledLiftable_alwaysAllowed
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (labels : TransitionMaskLabels Tag)
    {tag : Tag}
    (derive : base.TaggedDerives tag)
    (guarded forbidden : List Bool)
    (hvalid :
      (GeneralizedState.mk tag guarded forbidden).Valid
        atomCount queryCount) :
    LabelledLiftable base atomCount queryCount
      (fun _ => true) labels derive guarded forbidden := by
  induction derive generalizing guarded forbidden with
  | terminal hterminal =>
      exact .terminal hterminal guarded forbidden hvalid rfl
  | @rule parent children harity henabled hchildren ih =>
      apply LabelledLiftable.rule
        harity henabled hchildren guarded forbidden hvalid
      intro child hchild
      apply ih child hchild
      exact labelledChildState_valid labels parent child
        guarded forbidden hvalid

theorem baseDerives_lifts_to_labelled_alwaysAllowed
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (labels : TransitionMaskLabels Tag)
    {tag : Tag}
    (derive : base.TaggedDerives tag)
    (guarded forbidden : List Bool)
    (hvalid :
      (GeneralizedState.mk tag guarded forbidden).Valid
        atomCount queryCount) :
    (labelledGeneralizedStateRuleSystem
      base atomCount queryCount (fun _ => true) labels
    ).TaggedDerives
      ⟨GeneralizedState.mk tag guarded forbidden, hvalid⟩ := by
  exact (labelledLiftable_alwaysAllowed
    base atomCount queryCount labels derive
      guarded forbidden hvalid).toTaggedDerives

theorem LabelledLiftable.decideRequiredLabelled
    {base : NumberedRuleSystem Tag}
    {atomCount queryCount : Nat}
    {requirement : TerminalMaskRequirement Tag}
    {labels : TransitionMaskLabels Tag}
    {tag : Tag} {derive : base.TaggedDerives tag}
    {guarded forbidden : List Bool}
    (hlift :
      LabelledLiftable base atomCount queryCount
        (requiredMasksTerminal requirement atomCount queryCount)
        labels derive guarded forbidden) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
        ).states.decode index =
          some
            ⟨GeneralizedState.mk tag guarded forbidden,
              by
                cases hlift with
                | terminal _ _ _ hvalid _ => exact hvalid
                | rule _ _ _ _ _ hvalid _ => exact hvalid⟩ ∧
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true := by
  let initial :
      ValidGeneralizedState Tag atomCount queryCount :=
    ⟨GeneralizedState.mk tag guarded forbidden,
      by
        cases hlift with
        | terminal _ _ _ hvalid _ => exact hvalid
        | rule _ _ _ _ _ hvalid _ => exact hvalid⟩
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
  have hderive : system.TaggedDerives initial :=
    hlift.toTaggedDerives
  obtain ⟨index, hindex, hdecode⟩ :=
    system.states.exists_index_decode initial
  refine ⟨index, hdecode, ?_⟩
  exact
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).2
      ⟨initial, hdecode, hderive⟩

theorem baseDerives_decideRequiredLabelled_noRequirement
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (labels : TransitionMaskLabels Tag)
    {tag : Tag}
    (derive : base.TaggedDerives tag)
    (guarded forbidden : List Bool)
    (hvalid :
      (GeneralizedState.mk tag guarded forbidden).Valid
        atomCount queryCount) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount noTerminalMaskRequirement labels
        ).states.decode index =
          some ⟨GeneralizedState.mk tag guarded forbidden, hvalid⟩ ∧
      decideRequiredLabelledState
        base atomCount queryCount noTerminalMaskRequirement
        labels index = true := by
  have liftAlways :=
    labelledLiftable_alwaysAllowed
      base atomCount queryCount labels derive
      guarded forbidden hvalid
  have lift :
      LabelledLiftable base atomCount queryCount
        (requiredMasksTerminal noTerminalMaskRequirement
          atomCount queryCount)
        labels derive guarded forbidden := by
    simpa using liftAlways
  exact lift.decideRequiredLabelled

@[simp] theorem markAt_replicate_true
    (index count : Nat) :
    markAt index (List.replicate count true) =
      List.replicate count true := by
  induction index generalizing count with
  | zero =>
      cases count <;> rfl
  | succ index ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [List.replicate_succ, markAt, List.cons.injEq,
            true_and]
          exact ih count

@[simp] theorem markMany_replicate_true
    (indices : List Nat) (count : Nat) :
    markMany indices (List.replicate count true) =
      List.replicate count true := by
  induction indices with
  | nil =>
      rfl
  | cons index rest ih =>
      simp only [markMany]
      rw [markAt_replicate_true, ih]

theorem allIndicesMarked_replicate_true
    (indices : List Nat) (count : Nat)
    (hbounded : ∀ index ∈ indices, index < count) :
    allIndicesMarked indices (List.replicate count true) = true := by
  rw [allIndicesMarked_correct]
  intro index hindex
  simp [maskBit, hbounded index hindex]

/--
Every base derivation lifts to the required labelled system when started
with fully saturated masks, provided every terminal requirement names a
real bit.  This is the executable completeness endpoint for saturated
states; reaching saturation from a smaller initial mask is a separate
emission-coverage obligation.
-/
theorem baseDerives_lifts_to_requiredLabelled_saturated
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (hguarded :
      ∀ tag index, index ∈ requirement.guarded tag →
        index < atomCount)
    (hforbidden :
      ∀ tag index, index ∈ requirement.forbidden tag →
        index < queryCount)
    {tag : Tag}
    (derive : base.TaggedDerives tag) :
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
    ).TaggedDerives
      ⟨GeneralizedState.mk tag
          (List.replicate atomCount true)
          (List.replicate queryCount true),
        by simp [GeneralizedState.Valid]⟩ := by
  let guarded := List.replicate atomCount true
  let forbidden := List.replicate queryCount true
  have lift :
      LabelledLiftable base atomCount queryCount
        (requiredMasksTerminal requirement atomCount queryCount)
        labels derive guarded forbidden := by
    induction derive with
    | @terminal state hterminal =>
        exact LabelledLiftable.terminal hterminal guarded forbidden
          (by simp [guarded, forbidden, GeneralizedState.Valid])
          (by
            simp only [requiredMasksTerminal]
            rw [Bool.and_eq_true]
            exact
              ⟨allIndicesMarked_replicate_true
                (requirement.guarded state) atomCount
                (hguarded state),
              allIndicesMarked_replicate_true
                (requirement.forbidden state) queryCount
                (hforbidden state)⟩)
    | @rule parent children harity henabled hchildren ih =>
        apply LabelledLiftable.rule
          harity henabled hchildren guarded forbidden
        · simp [guarded, forbidden, GeneralizedState.Valid]
        · intro child hchild
          simpa [guarded, forbidden, labelledGuardedUpdate,
            labelledForbiddenUpdate] using ih child hchild
  exact lift.toTaggedDerives

theorem baseDerives_decideRequiredLabelled_saturated
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (hguarded :
      ∀ tag index, index ∈ requirement.guarded tag →
        index < atomCount)
    (hforbidden :
      ∀ tag index, index ∈ requirement.forbidden tag →
        index < queryCount)
    {tag : Tag}
    (derive : base.TaggedDerives tag) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
        ).states.decode index =
          some
            ⟨GeneralizedState.mk tag
                (List.replicate atomCount true)
                (List.replicate queryCount true),
              by simp [GeneralizedState.Valid]⟩ ∧
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true := by
  let saturated :
      ValidGeneralizedState Tag atomCount queryCount :=
    ⟨GeneralizedState.mk tag
        (List.replicate atomCount true)
        (List.replicate queryCount true),
      by simp [GeneralizedState.Valid]⟩
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
  have hderive : system.TaggedDerives saturated := by
    exact baseDerives_lifts_to_requiredLabelled_saturated
      base atomCount queryCount requirement labels
      hguarded hforbidden derive
  obtain ⟨index, hindex, hdecode⟩ :=
    system.states.exists_index_decode saturated
  refine ⟨index, hdecode, ?_⟩
  exact
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).2
      ⟨saturated, hdecode, hderive⟩

end NSSE
