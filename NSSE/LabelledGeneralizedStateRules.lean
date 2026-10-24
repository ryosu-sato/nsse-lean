import NSSE.GeneralizedStateTransitionRules
import NSSE.ResponseMask

/-!
# Finite labelled updates for generalized-state rules

A structural transition may discharge several guarded atoms and encounter
several canonical forbidden-query types at once.  Finite lists of bit
indices label the transition; the corresponding state update marks every
listed bit.
-/

namespace NSSE

universe u

def markMany : List Nat → List Bool → List Bool
  | [], mask => mask
  | index :: indices, mask =>
      markMany indices (markAt index mask)

theorem maskLe_markMany (indices : List Nat) (mask : List Bool) :
    MaskLe mask (markMany indices mask) := by
  induction indices generalizing mask with
  | nil =>
      exact MaskLe.refl mask
  | cons index indices ih =>
      exact (maskLe_markAt index mask).trans
        (ih (markAt index mask))

theorem markMany_monotone (indices : List Nat) :
    MaskMonotone (markMany indices) := by
  intro left right hle
  induction indices generalizing left right with
  | nil =>
      exact hle
  | cons index indices ih =>
      exact ih (markAt_monotone index hle)

theorem markMany_length (indices : List Nat) (mask : List Bool) :
    (markMany indices mask).length = mask.length := by
  exact (maskLe_markMany indices mask).length_eq.symm

theorem maskBit_markMany_of_mem
    (indices : List Nat) (mask : List Bool) (index : Nat)
    (hindex : index ∈ indices) (hbound : index < mask.length) :
    maskBit (markMany indices mask) index = true := by
  induction indices generalizing mask with
  | nil =>
      simp at hindex
  | cons first rest ih =>
      simp only [List.mem_cons] at hindex
      simp only [markMany]
      rcases hindex with rfl | hrest
      · apply (maskLe_markMany rest (markAt index mask)).maskBit_true
          index
        exact maskBit_markAt_self index mask hbound
      · apply ih (markAt first mask) hrest
        rw [← (maskLe_markAt first mask).length_eq]
        exact hbound

structure TransitionMaskLabels (Tag : Type u) where
  guarded : Tag → Tag → List Nat
  forbidden : Tag → Tag → List Nat

def allIndicesMarked (indices : List Nat) (mask : List Bool) : Bool :=
  indices.all fun index => maskBit mask index

theorem allIndicesMarked_correct
    (indices : List Nat) (mask : List Bool) :
    allIndicesMarked indices mask = true ↔
      ∀ index ∈ indices, maskBit mask index = true := by
  simp [allIndicesMarked]

structure TerminalMaskRequirement (Tag : Type u) where
  guarded : Tag → List Nat
  forbidden : Tag → List Nat

def noTerminalMaskRequirement : TerminalMaskRequirement Tag where
  guarded := fun _ => []
  forbidden := fun _ => []

def requiredMasksTerminal
    (requirement : TerminalMaskRequirement Tag)
    (atomCount queryCount : Nat)
    (state : ValidGeneralizedState Tag atomCount queryCount) : Bool :=
  allIndicesMarked
      (requirement.guarded state.1.tag) state.1.guarded &&
    allIndicesMarked
      (requirement.forbidden state.1.tag) state.1.forbidden

@[simp] theorem requiredMasksTerminal_noRequirement
    (atomCount queryCount : Nat)
    (state : ValidGeneralizedState Tag atomCount queryCount) :
    requiredMasksTerminal noTerminalMaskRequirement
      atomCount queryCount state = true := by
  simp [requiredMasksTerminal, noTerminalMaskRequirement,
    allIndicesMarked]

theorem requiredMasksTerminal_correct
    (requirement : TerminalMaskRequirement Tag)
    (atomCount queryCount : Nat)
    (state : ValidGeneralizedState Tag atomCount queryCount) :
    requiredMasksTerminal requirement atomCount queryCount state = true ↔
      (∀ index ∈ requirement.guarded state.1.tag,
        maskBit state.1.guarded index = true) ∧
      (∀ index ∈ requirement.forbidden state.1.tag,
        maskBit state.1.forbidden index = true) := by
  simp [requiredMasksTerminal, allIndicesMarked_correct]

def labelledGuardedUpdate
    (labels : TransitionMaskLabels Tag) :
    Tag → Tag → List Bool → List Bool :=
  fun parent child mask =>
    markMany (labels.guarded parent child) mask

def labelledForbiddenUpdate
    (labels : TransitionMaskLabels Tag) :
    Tag → Tag → List Bool → List Bool :=
  fun parent child mask =>
    markMany (labels.forbidden parent child) mask

theorem labelledFollow_marks_guarded
    (labels : TransitionMaskLabels Tag)
    (parent child : GeneralizedState Tag)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent [child] = true)
    (index : Nat)
    (hindex : index ∈ labels.guarded parent.tag child.tag)
    (hbound : index < parent.guarded.length) :
    maskBit child.guarded index = true := by
  rw [allStateMasksFollow_correct] at hfollow
  rw [(hfollow child (by simp)).1]
  exact maskBit_markMany_of_mem
    (labels.guarded parent.tag child.tag)
    parent.guarded index hindex hbound

theorem labelledFollow_marks_forbidden
    (labels : TransitionMaskLabels Tag)
    (parent child : GeneralizedState Tag)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent [child] = true)
    (index : Nat)
    (hindex : index ∈ labels.forbidden parent.tag child.tag)
    (hbound : index < parent.forbidden.length) :
    maskBit child.forbidden index = true := by
  rw [allStateMasksFollow_correct] at hfollow
  rw [(hfollow child (by simp)).2]
  exact maskBit_markMany_of_mem
    (labels.forbidden parent.tag child.tag)
    parent.forbidden index hindex hbound

def labelledGeneralizedStateRuleSystem
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (labels : TransitionMaskLabels Tag) :
    NumberedRuleSystem
      (ValidGeneralizedState Tag atomCount queryCount) :=
  transitionGeneralizedStateRuleSystem
    base atomCount queryCount terminalAllowed
      (labelledGuardedUpdate labels)
      (labelledForbiddenUpdate labels)

def requiredLabelledGeneralizedStateRuleSystem
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag) :
    NumberedRuleSystem
      (ValidGeneralizedState Tag atomCount queryCount) :=
  labelledGeneralizedStateRuleSystem
    base atomCount queryCount
      (requiredMasksTerminal requirement atomCount queryCount)
      labels

theorem requiredLabelled_enabled_iff
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (parent : ValidGeneralizedState Tag atomCount queryCount)
    (children :
      List (ValidGeneralizedState Tag atomCount queryCount)) :
    (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels).enabled
          parent children = true ↔
      base.enabled parent.1.tag
          (children.map fun child => child.1.tag) = true ∧
        allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent.1 (children.map Subtype.val) = true := by
  simp [requiredLabelledGeneralizedStateRuleSystem,
    labelledGeneralizedStateRuleSystem,
    transitionGeneralizedStateRuleSystem]

theorem requiredLabelled_terminal_iff
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (state : ValidGeneralizedState Tag atomCount queryCount) :
    (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels).terminal state =
        true ↔
      base.terminal state.1.tag = true ∧
      (∀ index ∈ requirement.guarded state.1.tag,
        maskBit state.1.guarded index = true) ∧
      (∀ index ∈ requirement.forbidden state.1.tag,
        maskBit state.1.forbidden index = true) := by
  simp [requiredLabelledGeneralizedStateRuleSystem,
    labelledGeneralizedStateRuleSystem,
    transitionGeneralizedStateRuleSystem,
    requiredMasksTerminal_correct]

theorem labelledGeneralizedStateRuleSystem_derives_monotone
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (labels : TransitionMaskLabels Tag)
    {state : ValidGeneralizedState Tag atomCount queryCount}
    (derive :
      (labelledGeneralizedStateRuleSystem base atomCount queryCount
        terminalAllowed labels).TaggedDerives state) :
    (generalizedStateRuleSystem base atomCount queryCount
      terminalAllowed).TaggedDerives state := by
  exact transitionGeneralizedStateRuleSystem_derives_monotone
    base atomCount queryCount terminalAllowed
      (labelledGuardedUpdate labels)
      (labelledForbiddenUpdate labels)
      (fun _ _ => maskLe_markMany _)
      (fun _ _ => maskLe_markMany _)
      derive

theorem labelledGeneralizedStateRuleSystem_derives_base
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (labels : TransitionMaskLabels Tag)
    {state : ValidGeneralizedState Tag atomCount queryCount}
    (derive :
      (labelledGeneralizedStateRuleSystem base atomCount queryCount
        terminalAllowed labels).TaggedDerives state) :
    base.TaggedDerives state.1.tag := by
  exact generalizedStateRuleSystem_derives_base
    base atomCount queryCount terminalAllowed
      (labelledGeneralizedStateRuleSystem_derives_monotone
        base atomCount queryCount terminalAllowed labels derive)

def decideRequiredLabelledState
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (index : Nat) : Bool :=
  decideHornState
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels).compiler
    index

theorem decideRequiredLabelledState_correct
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels).states.stateCount) :
    decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true ↔
      ∃ state,
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels).states.decode
            index = some state ∧
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels).TaggedDerives
            state := by
  exact NumberedRuleSystem.decideState_correct
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels)
    index hindex

theorem decideRequiredLabelledState_sound
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (meaning :
      ValidGeneralizedState Tag atomCount queryCount → Prop)
    (terminal_sound :
      ∀ state,
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels).terminal state =
            true →
        meaning state)
    (rule_sound :
      ∀ parent children,
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels).enabled
            parent children = true →
        (∀ child ∈ children, meaning child) →
        meaning parent)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true) :
    ∃ state,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels).states.decode
          index = some state ∧
      meaning state := by
  obtain ⟨state, hdecode, hderive⟩ :=
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).1
      haccept
  exact ⟨state, hdecode,
    hderive.sound meaning terminal_sound rule_sound⟩

end NSSE
