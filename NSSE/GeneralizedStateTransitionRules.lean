import NSSE.GeneralizedStateRuleSystem

/-!
# Transition-specific updates of generalized-state masks

This layer refines the merely monotone generalized-state rules by requiring
each child mask to be exactly the result of an executable update selected by
the parent and child tags.
-/

namespace NSSE

universe u

def maskEqB : List Bool → List Bool → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      (left == right) && maskEqB lefts rights
  | _, _ => false

theorem maskEqB_correct (left right : List Bool) :
    maskEqB left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [maskEqB]
  | cons bit rest ih =>
      cases right with
      | nil => simp [maskEqB]
      | cons other others =>
          simp only [maskEqB, Bool.and_eq_true, ih,
            beq_iff_eq]
          constructor
          · rintro ⟨rfl, rfl⟩
            rfl
          · intro h
            cases h
            exact ⟨rfl, rfl⟩

def allStateMasksFollow
    (guardedUpdate forbiddenUpdate :
      Tag → Tag → List Bool → List Bool)
    (parent : GeneralizedState Tag)
    (children : List (GeneralizedState Tag)) : Bool :=
  children.all fun child =>
    maskEqB child.guarded
        (guardedUpdate parent.tag child.tag parent.guarded) &&
      maskEqB child.forbidden
        (forbiddenUpdate parent.tag child.tag parent.forbidden)

theorem allStateMasksFollow_correct
    (guardedUpdate forbiddenUpdate :
      Tag → Tag → List Bool → List Bool)
    (parent : GeneralizedState Tag)
    (children : List (GeneralizedState Tag)) :
    allStateMasksFollow guardedUpdate forbiddenUpdate
        parent children = true ↔
      ∀ child ∈ children,
        child.guarded =
            guardedUpdate parent.tag child.tag parent.guarded ∧
          child.forbidden =
            forbiddenUpdate parent.tag child.tag parent.forbidden := by
  simp [allStateMasksFollow, maskEqB_correct]

def transitionGeneralizedStateRuleSystem
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (guardedUpdate forbiddenUpdate :
      Tag → Tag → List Bool → List Bool) :
    NumberedRuleSystem
      (ValidGeneralizedState Tag atomCount queryCount) where
  states :=
    validGeneralizedStateEnumeration
      base.states atomCount queryCount
  arities := base.arities
  terminal state :=
    base.terminal state.1.tag && terminalAllowed state
  enabled parent children :=
    base.enabled parent.1.tag
        (children.map fun child => child.1.tag) &&
      allStateMasksFollow guardedUpdate forbiddenUpdate
        parent.1 (children.map Subtype.val)

theorem transitionGeneralizedStateRuleSystem_derives_monotone
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (guardedUpdate forbiddenUpdate :
      Tag → Tag → List Bool → List Bool)
    (hguarded :
      ∀ parent child mask,
        MaskLe mask (guardedUpdate parent child mask))
    (hforbidden :
      ∀ parent child mask,
        MaskLe mask (forbiddenUpdate parent child mask))
    {state : ValidGeneralizedState Tag atomCount queryCount}
    (derive :
      (transitionGeneralizedStateRuleSystem base atomCount queryCount
        terminalAllowed guardedUpdate forbiddenUpdate).TaggedDerives
          state) :
    (generalizedStateRuleSystem base atomCount queryCount
      terminalAllowed).TaggedDerives state := by
  induction derive with
  | terminal hterminal =>
      apply NumberedRuleSystem.TaggedDerives.terminal
        (system :=
          generalizedStateRuleSystem base atomCount queryCount
            terminalAllowed)
      simpa [transitionGeneralizedStateRuleSystem,
        generalizedStateRuleSystem] using hterminal
  | @rule parent children harity henabled hchildren ih =>
      apply NumberedRuleSystem.TaggedDerives.rule
        (system :=
          generalizedStateRuleSystem base atomCount queryCount
            terminalAllowed)
        (by
          simpa [transitionGeneralizedStateRuleSystem,
            generalizedStateRuleSystem] using harity)
      · simp only [transitionGeneralizedStateRuleSystem,
          Bool.and_eq_true] at henabled
        simp only [generalizedStateRuleSystem, Bool.and_eq_true]
        refine ⟨henabled.1, ?_⟩
        rw [allStateMasksGrow_correct]
        rw [allStateMasksFollow_correct] at henabled
        intro child hchild
        obtain ⟨hguardedEq, hforbiddenEq⟩ :=
          henabled.2 child hchild
        constructor
        · rw [hguardedEq]
          exact hguarded parent.1.tag child.tag parent.1.guarded
        · rw [hforbiddenEq]
          exact hforbidden parent.1.tag child.tag parent.1.forbidden
      · exact ih

theorem transitionGeneralizedStateRuleSystem_derives_base
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    (guardedUpdate forbiddenUpdate :
      Tag → Tag → List Bool → List Bool)
    (hguarded :
      ∀ parent child mask,
        MaskLe mask (guardedUpdate parent child mask))
    (hforbidden :
      ∀ parent child mask,
        MaskLe mask (forbiddenUpdate parent child mask))
    {state : ValidGeneralizedState Tag atomCount queryCount}
    (derive :
      (transitionGeneralizedStateRuleSystem base atomCount queryCount
        terminalAllowed guardedUpdate forbiddenUpdate).TaggedDerives
          state) :
    base.TaggedDerives state.1.tag := by
  apply generalizedStateRuleSystem_derives_base
    base atomCount queryCount terminalAllowed
  exact transitionGeneralizedStateRuleSystem_derives_monotone
    base atomCount queryCount terminalAllowed
      guardedUpdate forbiddenUpdate hguarded hforbidden derive

end NSSE
