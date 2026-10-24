import NSSE.NumberedTaggedCompiler

/-!
# Numbered rules over mask-refined generalized states

The finite tag compiler is lifted to states carrying fixed-length guarded
atom and forbidden-query masks.  Along a rule, both masks may only grow
from parent to child.
-/

namespace NSSE

universe u

theorem length_eq_of_mem_boolVectors
    {count : Nat} {bits : List Bool}
    (hbits : bits ∈ boolVectors count) :
    bits.length = count := by
  induction count generalizing bits with
  | zero =>
      simp [boolVectors] at hbits
      subst bits
      rfl
  | succ count ih =>
      simp only [boolVectors, List.mem_append,
        List.mem_map] at hbits
      rcases hbits with ⟨tail, htail, rfl⟩ |
          ⟨tail, htail, rfl⟩
      · simp [ih htail]
      · simp [ih htail]

theorem valid_of_mem_enumerateStates
    {tags : List Tag} {atomCount queryCount : Nat}
    {state : GeneralizedState Tag}
    (hstate :
      state ∈ enumerateStates tags atomCount queryCount) :
    state.Valid atomCount queryCount := by
  rcases state with ⟨tag, guarded, forbidden⟩
  simp only [enumerateStates, List.mem_flatMap,
    List.mem_map] at hstate
  obtain ⟨foundTag, htag, foundGuarded, hguarded,
    foundForbidden, hforbidden, heq⟩ := hstate
  cases heq
  exact ⟨length_eq_of_mem_boolVectors hguarded,
    length_eq_of_mem_boolVectors hforbidden⟩

def ValidGeneralizedState
    (Tag : Type u) (atomCount queryCount : Nat) :=
  {state : GeneralizedState Tag //
    state.Valid atomCount queryCount}

def validGeneralizedStateEnumeration
    (tags : Enumeration Tag) (atomCount queryCount : Nat) :
    Enumeration
      (ValidGeneralizedState Tag atomCount queryCount) where
  values :=
    (enumerateStates tags.values atomCount queryCount).attach.map
      fun state =>
        ⟨state.1, valid_of_mem_enumerateStates state.2⟩
  complete := by
    intro state
    simp only [List.mem_map]
    have hmem :=
      mem_enumerateStates tags atomCount queryCount
        state.1 state.2
    let attached :
        {candidate : GeneralizedState Tag //
          candidate ∈
            enumerateStates tags.values atomCount queryCount} :=
      ⟨state.1, hmem⟩
    refine ⟨attached, List.mem_attach _ attached, ?_⟩
    exact Subtype.ext rfl

def maskLeB : List Bool → List Bool → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      (!left || right) && maskLeB lefts rights
  | _, _ => false

theorem maskLeB_correct
    (left right : List Bool) :
    maskLeB left right = true ↔ MaskLe left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          constructor
          · intro _
            exact .nil
          · intro _
            rfl
      | cons bit rest =>
          constructor
          · simp [maskLeB]
          · intro h
            cases h
  | cons bit rest ih =>
      cases right with
      | nil =>
          constructor
          · simp [maskLeB]
          · intro h
            cases h
      | cons other others =>
          simp only [maskLeB, Bool.and_eq_true,
            Bool.or_eq_true, Bool.not_eq_true, ih]
          constructor
          · rintro ⟨hhead, htail⟩
            apply MaskLe.cons
            · intro hbit
              cases bit <;> cases other <;> simp_all
            · exact htail
          · intro h
            cases h with
            | cons hhead htail =>
                constructor
                · cases bit <;> cases other <;> simp_all
                · exact htail

def allStateMasksGrow
    (parent : GeneralizedState Tag)
    (children : List (GeneralizedState Tag)) : Bool :=
  children.all fun child =>
    maskLeB parent.guarded child.guarded &&
      maskLeB parent.forbidden child.forbidden

theorem allStateMasksGrow_correct
    (parent : GeneralizedState Tag)
    (children : List (GeneralizedState Tag)) :
    allStateMasksGrow parent children = true ↔
      ∀ child ∈ children,
        MaskLe parent.guarded child.guarded ∧
        MaskLe parent.forbidden child.forbidden := by
  simp [allStateMasksGrow, maskLeB_correct]

def generalizedStateRuleSystem
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool) :
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
      allStateMasksGrow parent.1
        (children.map Subtype.val)

theorem generalizedStateRuleSystem_derives_base
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (terminalAllowed :
      ValidGeneralizedState Tag atomCount queryCount → Bool)
    {state : ValidGeneralizedState Tag atomCount queryCount}
    (derive :
      (generalizedStateRuleSystem base atomCount queryCount
        terminalAllowed).TaggedDerives state) :
    base.TaggedDerives state.1.tag := by
  induction derive with
  | terminal hterminal =>
      apply NumberedRuleSystem.TaggedDerives.terminal
      simp only [generalizedStateRuleSystem,
        Bool.and_eq_true] at hterminal
      exact hterminal.1
  | @rule parent children harity henabled hchildren ih =>
      let projected :=
        children.map fun child => child.1.tag
      apply NumberedRuleSystem.TaggedDerives.rule
        (children := projected)
      · simpa [projected, generalizedStateRuleSystem] using harity
      · simp only [generalizedStateRuleSystem,
          Bool.and_eq_true] at henabled
        exact henabled.1
      · intro tag htag
        simp only [projected, List.mem_map] at htag
        obtain ⟨child, hchild, rfl⟩ := htag
        exact ih child hchild

end NSSE
