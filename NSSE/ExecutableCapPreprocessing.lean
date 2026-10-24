import NSSE.ExecutableProductivity
import NSSE.HeterogeneousCapComponents

/-!
# Executable removal of empty-right cap components

The right language of a retained component must be nonempty.  For finite
DFAs this is exactly productivity of the start state, so the executable Horn
table either constructs the required witness or certifies that the component
can never cover a word.
-/

namespace NSSE

universe u

theorem not_capComponentCovers_of_right_empty
    (component : CapComponent α)
    (hright : ¬ ∃ word, component.right word)
    (word : Word α) :
    ¬ capComponentCovers component word := by
  rintro ⟨tail, leftWord, cappedWord, _,
    _hleft, mu, _power, _remainder, hmu, _⟩
  exact hright ⟨mu, hmu⟩

structure ExecutableFiniteCapPair (α : Type u) where
  leftCount : Nat
  rightCount : Nat
  left : DFA α (Fin leftCount)
  right : DFA α (Fin rightCount)
  leftAcceptDecidable :
    ∀ state, Decidable (left.accept state)
  rightAcceptDecidable :
    ∀ state, Decidable (right.accept state)

namespace ExecutableFiniteCapPair

def capComponent (component : ExecutableFiniteCapPair α) :
    CapComponent α :=
  CapComponent.ofDFA component.left component.right

def rightIsProductive
    [Fintype α] [DecidableEq α]
    (component : ExecutableFiniteCapPair α) : Bool := by
  letI : ∀ state, Decidable (component.right.accept state) :=
    component.rightAcceptDecidable
  exact
    component.right.productivityGame.decideWinning
      component.right.start.val

theorem rightIsProductive_iff
    [Fintype α] [DecidableEq α]
    (component : ExecutableFiniteCapPair α) :
    component.rightIsProductive = true ↔
      ∃ word, component.right.language word := by
  letI : ∀ state, Decidable (component.right.accept state) :=
    component.rightAcceptDecidable
  rw [rightIsProductive,
    component.right.productivityGame.decideWinning_correct
      component.right.start.val component.right.start.isLt,
    component.right.productivityGame_winning_iff
      component.right.start]
  rfl

noncomputable def retainIfRightNonempty
    [Fintype α] [DecidableEq α]
    (component : ExecutableFiniteCapPair α) :
    Option (FiniteProductiveCapPair α) := by
  letI : ∀ state, Decidable (component.left.accept state) :=
    component.leftAcceptDecidable
  letI : ∀ state, Decidable (component.right.accept state) :=
    component.rightAcceptDecidable
  if hproductive : component.rightIsProductive = true then
    exact some
      { leftCount := component.leftCount
        rightCount := component.rightCount
        left := component.left.executableProductive
        right := component.right.executableProductive
        right_nonempty :=
          component.rightIsProductive_iff.mp hproductive }
  else
    exact none

theorem retained_capComponent_eq
    [Fintype α] [DecidableEq α]
    (component : ExecutableFiniteCapPair α)
    (retained : FiniteProductiveCapPair α)
    (hretained :
      component.retainIfRightNonempty = some retained) :
    retained.capComponent = component.capComponent := by
  letI : ∀ state, Decidable (component.left.accept state) :=
    component.leftAcceptDecidable
  letI : ∀ state, Decidable (component.right.accept state) :=
    component.rightAcceptDecidable
  unfold retainIfRightNonempty at hretained
  split at hretained
  next hproductive =>
    simp only [Option.some.injEq] at hretained
    subst retained
    rfl
  next hproductive =>
    simp at hretained

theorem retainIfRightNonempty_eq_none_iff
    [Fintype α] [DecidableEq α]
    (component : ExecutableFiniteCapPair α) :
    component.retainIfRightNonempty = none ↔
      ¬ ∃ word, component.right.language word := by
  by_cases hproductive : component.rightIsProductive = true
  · have hnonempty :=
      component.rightIsProductive_iff.mp hproductive
    simp [retainIfRightNonempty, hproductive, hnonempty]
  · have hempty :
        ¬ ∃ word, component.right.language word := by
      exact fun hnonempty =>
        hproductive
          (component.rightIsProductive_iff.mpr hnonempty)
    simp [retainIfRightNonempty, hproductive, hempty]

theorem not_covers_of_retainIfRightNonempty_eq_none
    [Fintype α] [DecidableEq α]
    (component : ExecutableFiniteCapPair α)
    (hremoved : component.retainIfRightNonempty = none)
    (word : Word α) :
    ¬ capComponentCovers component.capComponent word := by
  apply not_capComponentCovers_of_right_empty
  exact
    (component.retainIfRightNonempty_eq_none_iff).1 hremoved

end ExecutableFiniteCapPair

def ExecutableCapFamilyCovers
    (components : List (ExecutableFiniteCapPair α))
    (word : Word α) : Prop :=
  match components with
  | [] => False
  | component :: components =>
      capComponentCovers component.capComponent word ∨
        ExecutableCapFamilyCovers components word

noncomputable def retainRightNonemptyComponents
    [Fintype α] [DecidableEq α] :
    List (ExecutableFiniteCapPair α) →
      List (FiniteProductiveCapPair α)
  | [] => []
  | component :: components =>
      match component.retainIfRightNonempty with
      | some retained =>
          retained :: retainRightNonemptyComponents components
      | none =>
          retainRightNonemptyComponents components

theorem heterogeneousCapFamilyCovers_retainRightNonempty_iff
    [Fintype α] [DecidableEq α]
    (components : List (ExecutableFiniteCapPair α))
    (word : Word α) :
    HeterogeneousCapFamilyCovers
        (retainRightNonemptyComponents components) word ↔
      ExecutableCapFamilyCovers components word := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      rw [retainRightNonemptyComponents]
      cases hretained :
          component.retainIfRightNonempty with
      | none =>
          rw [ExecutableCapFamilyCovers]
          have hnotCovered :=
            component.not_covers_of_retainIfRightNonempty_eq_none
              hretained word
          tauto
      | some retained =>
          rw [HeterogeneousCapFamilyCovers,
            ExecutableCapFamilyCovers,
            component.retained_capComponent_eq
              retained hretained,
            ih]

end NSSE
