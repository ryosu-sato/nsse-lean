import NSSE.UncheckedExecutableCapCoveragePresburger
import NSSE.DFAReindexing

/-!
# Unchecked cap coverage from arbitrary finite state types

The input boundary now requires neither `Fin` state presentations nor
right-language nonemptiness proofs.  State types and acceptance decision
procedures are packaged per component, reindexed, and then passed through the
executable empty-right preprocessing.
-/

namespace NSSE

universe u v w

structure UncheckedPackagedFiniteCapPair (α : Type u) where
  LeftState : Type v
  RightState : Type w
  leftFintype : Fintype LeftState
  rightFintype : Fintype RightState
  left : DFA α LeftState
  right : DFA α RightState
  leftAcceptDecidable :
    ∀ state, Decidable (left.accept state)
  rightAcceptDecidable :
    ∀ state, Decidable (right.accept state)

namespace UncheckedPackagedFiniteCapPair

def capComponent
    (component : UncheckedPackagedFiniteCapPair α) :
    CapComponent α :=
  CapComponent.ofDFA component.left component.right

noncomputable def toExecutableFinite
    (component : UncheckedPackagedFiniteCapPair α) :
    ExecutableFiniteCapPair α := by
  letI : Fintype component.LeftState := component.leftFintype
  letI : Fintype component.RightState := component.rightFintype
  let leftEquiv := Fintype.equivFin component.LeftState
  let rightEquiv := Fintype.equivFin component.RightState
  exact
    { leftCount := Fintype.card component.LeftState
      rightCount := Fintype.card component.RightState
      left := component.left.reindex leftEquiv
      right := component.right.reindex rightEquiv
      leftAcceptDecidable := fun state =>
        component.leftAcceptDecidable (leftEquiv.symm state)
      rightAcceptDecidable := fun state =>
        component.rightAcceptDecidable (rightEquiv.symm state) }

@[simp] theorem toExecutableFinite_capComponent
    (component : UncheckedPackagedFiniteCapPair α) :
    component.toExecutableFinite.capComponent =
      component.capComponent := by
  letI : Fintype component.LeftState := component.leftFintype
  letI : Fintype component.RightState := component.rightFintype
  let leftEquiv := Fintype.equivFin component.LeftState
  let rightEquiv := Fintype.equivFin component.RightState
  change
    CapComponent.ofDFA
        (component.left.reindex leftEquiv)
        (component.right.reindex rightEquiv) =
      CapComponent.ofDFA component.left component.right
  unfold CapComponent.ofDFA
  congr
  · exact component.left.reindex_language leftEquiv
  · exact component.right.reindex_language rightEquiv

end UncheckedPackagedFiniteCapPair

def UncheckedPackagedCapFamilyCovers
    (components : List (UncheckedPackagedFiniteCapPair α))
    (word : Word α) : Prop :=
  match components with
  | [] => False
  | component :: components =>
      capComponentCovers component.capComponent word ∨
        UncheckedPackagedCapFamilyCovers components word

noncomputable def uncheckedPackagedComponentsToFinite
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    List (ExecutableFiniteCapPair α) :=
  components.map
    UncheckedPackagedFiniteCapPair.toExecutableFinite

theorem executableCapFamilyCovers_of_uncheckedPackaged_iff
    (components : List (UncheckedPackagedFiniteCapPair α))
    (word : Word α) :
    ExecutableCapFamilyCovers
        (uncheckedPackagedComponentsToFinite components) word ↔
      UncheckedPackagedCapFamilyCovers components word := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      unfold uncheckedPackagedComponentsToFinite at ih
      rw [uncheckedPackagedComponentsToFinite,
        List.map_cons, ExecutableCapFamilyCovers,
        UncheckedPackagedCapFamilyCovers,
        component.toExecutableFinite_capComponent, ih]

namespace LinearWordFamily

noncomputable def uncheckedPackagedCapFamilyCoverageFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    NatPresburger arity :=
  family.uncheckedExecutableCapFamilyCoverageFormula
    (uncheckedPackagedComponentsToFinite components)

theorem eval_uncheckedPackagedCapFamilyCoverageFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    (family.uncheckedPackagedCapFamilyCoverageFormula
      components).Eval parameters ↔
      UncheckedPackagedCapFamilyCovers components
        (family.word parameters) := by
  rw [uncheckedPackagedCapFamilyCoverageFormula,
    family.eval_uncheckedExecutableCapFamilyCoverageFormula_iff
      hnonempty parameters
      (uncheckedPackagedComponentsToFinite components),
    executableCapFamilyCovers_of_uncheckedPackaged_iff]

noncomputable def uncheckedPackagedCapFamilyUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    NatPresburger arity :=
  .neg
    (family.uncheckedPackagedCapFamilyCoverageFormula components)

theorem eval_uncheckedPackagedCapFamilyUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    (family.uncheckedPackagedCapFamilyUncoveredFormula
      components).Eval parameters ↔
      ¬ UncheckedPackagedCapFamilyCovers components
        (family.word parameters) := by
  rw [uncheckedPackagedCapFamilyUncoveredFormula,
    NatPresburger.Eval,
    family.eval_uncheckedPackagedCapFamilyCoverageFormula_iff
      hnonempty parameters components]

noncomputable def uncheckedPackagedExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.uncheckedPackagedCapFamilyUncoveredFormula components)

theorem eval_uncheckedPackagedExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    (family.uncheckedPackagedExistsUncoveredFormula
      components).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        ¬ UncheckedPackagedCapFamilyCovers components
          (family.word parameters) := by
  rw [uncheckedPackagedExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_uncheckedPackagedCapFamilyUncoveredFormula_iff
        hnonempty parameters components).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_uncheckedPackagedCapFamilyUncoveredFormula_iff
        hnonempty parameters components).2 huncovered⟩

noncomputable def uncheckedPackagedAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.uncheckedPackagedCapFamilyCoverageFormula components)

theorem eval_uncheckedPackagedAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (UncheckedPackagedFiniteCapPair α)) :
    (family.uncheckedPackagedAllCoveredFormula
      components).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        UncheckedPackagedCapFamilyCovers components
          (family.word parameters) := by
  rw [uncheckedPackagedAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_uncheckedPackagedCapFamilyCoverageFormula_iff
        hnonempty parameters components).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_uncheckedPackagedCapFamilyCoverageFormula_iff
        hnonempty parameters components).2
        (hcovered parameters)

end LinearWordFamily

end NSSE
