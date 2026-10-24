import NSSE.ExecutableProductivity
import NSSE.PackagedFiniteAutomataPresburger

/-!
# Executable productivity at the packaged input boundary

This package additionally stores decision procedures for the two accepting
predicates.  After finite-state reindexing, the Horn reachability algorithm
constructs both certified productivity tables.
-/

namespace NSSE

universe u v w

structure ExecutablePackagedFiniteCapPair (α : Type u) where
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
  right_nonempty : ∃ word, right.language word

namespace ExecutablePackagedFiniteCapPair

def capComponent
    (component : ExecutablePackagedFiniteCapPair α) :
    CapComponent α :=
  CapComponent.ofDFA component.left component.right

noncomputable def toFiniteProductiveCapPair
    [Fintype α] [DecidableEq α]
    (component : ExecutablePackagedFiniteCapPair α) :
    FiniteProductiveCapPair α := by
  letI : Fintype component.LeftState := component.leftFintype
  letI : Fintype component.RightState := component.rightFintype
  let leftEquiv := Fintype.equivFin component.LeftState
  let rightEquiv := Fintype.equivFin component.RightState
  let leftFin := component.left.reindex leftEquiv
  let rightFin := component.right.reindex rightEquiv
  letI : ∀ state, Decidable (leftFin.accept state) :=
    fun state =>
      component.leftAcceptDecidable (leftEquiv.symm state)
  letI : ∀ state, Decidable (rightFin.accept state) :=
    fun state =>
      component.rightAcceptDecidable (rightEquiv.symm state)
  exact
    { leftCount := Fintype.card component.LeftState
      rightCount := Fintype.card component.RightState
      left := leftFin.executableProductive
      right := rightFin.executableProductive
      right_nonempty := by
        rw [rightFin.executableProductive_language,
          component.right.reindex_language rightEquiv]
        exact component.right_nonempty }

@[simp] theorem toFiniteProductiveCapPair_capComponent
    [Fintype α] [DecidableEq α]
    (component : ExecutablePackagedFiniteCapPair α) :
    component.toFiniteProductiveCapPair.capComponent =
      component.capComponent := by
  letI : Fintype component.LeftState := component.leftFintype
  letI : Fintype component.RightState := component.rightFintype
  let leftEquiv := Fintype.equivFin component.LeftState
  let rightEquiv := Fintype.equivFin component.RightState
  letI :
      ∀ state,
        Decidable ((component.left.reindex leftEquiv).accept state) :=
    fun state =>
      component.leftAcceptDecidable (leftEquiv.symm state)
  letI :
      ∀ state,
        Decidable ((component.right.reindex rightEquiv).accept state) :=
    fun state =>
      component.rightAcceptDecidable (rightEquiv.symm state)
  change
    automataCapComponent
        ((component.left.reindex leftEquiv).executableProductive)
        ((component.right.reindex rightEquiv).executableProductive) =
      CapComponent.ofDFA component.left component.right
  unfold automataCapComponent ProductiveDFA.language
    CapComponent.ofDFA
  congr
  · exact component.left.reindex_language leftEquiv
  · exact component.right.reindex_language rightEquiv

end ExecutablePackagedFiniteCapPair

noncomputable def executablePackagedComponentsToFinite
    [Fintype α] [DecidableEq α]
    (components : List (ExecutablePackagedFiniteCapPair α)) :
    List (FiniteProductiveCapPair α) :=
  components.map
    ExecutablePackagedFiniteCapPair.toFiniteProductiveCapPair

def executablePackagedAutomataCapExpression
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    CapExpression α where
  caps :=
    components.map ExecutablePackagedFiniteCapPair.capComponent
  routes := routes.map fun route => route.automaton.language

theorem fullyHeterogeneousExpression_of_executablePackaged_eq
    [Fintype α] [DecidableEq α]
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    LinearWordFamily.fullyHeterogeneousAutomataCapExpression
        (executablePackagedComponentsToFinite components)
        (packagedRoutesToFinite routes) =
      executablePackagedAutomataCapExpression components routes := by
  unfold LinearWordFamily.fullyHeterogeneousAutomataCapExpression
    executablePackagedAutomataCapExpression
    executablePackagedComponentsToFinite packagedRoutesToFinite
  rw [List.map_map, List.map_map]
  have hcomponents :
      (fun component : ExecutablePackagedFiniteCapPair α =>
        component.toFiniteProductiveCapPair.capComponent) =
      (fun component : ExecutablePackagedFiniteCapPair α =>
        component.capComponent) := by
    funext component
    exact component.toFiniteProductiveCapPair_capComponent
  have hroutes :
      (fun route : PackagedFiniteDFA α =>
        route.toFiniteDFA.automaton.language) =
      (fun route : PackagedFiniteDFA α =>
        route.automaton.language) := by
    funext route
    exact route.toFiniteDFA_language
  simp only [Function.comp_def]
  rw [hcomponents, hroutes]

namespace LinearWordFamily

noncomputable def executablePackagedCoverageFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  family.fullyHeterogeneousExpressionCoverageFormula
    (executablePackagedComponentsToFinite components)
    (packagedRoutesToFinite routes)

theorem eval_executablePackagedCoverageFormula_iff_covers
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.executablePackagedCoverageFormula
      components routes).Eval parameters ↔
      (executablePackagedAutomataCapExpression
        components routes).Covers (family.word parameters) := by
  rw [executablePackagedCoverageFormula,
    family.eval_fullyHeterogeneousExpressionCoverageFormula_iff_covers
      hnonempty parameters
      (executablePackagedComponentsToFinite components)
      (packagedRoutesToFinite routes),
    fullyHeterogeneousExpression_of_executablePackaged_eq]

noncomputable def executablePackagedUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  .neg (family.executablePackagedCoverageFormula
    components routes)

theorem eval_executablePackagedUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.executablePackagedUncoveredFormula
      components routes).Eval parameters ↔
      (executablePackagedAutomataCapExpression
        components routes).Uncovered (family.word parameters) := by
  rw [executablePackagedUncoveredFormula,
    NatPresburger.Eval,
    family.eval_executablePackagedCoverageFormula_iff_covers
      hnonempty parameters components routes]
  rfl

noncomputable def executablePackagedExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.executablePackagedUncoveredFormula components routes)

theorem eval_executablePackagedExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.executablePackagedExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (executablePackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [executablePackagedExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_executablePackagedUncoveredFormula_iff
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_executablePackagedUncoveredFormula_iff
        hnonempty parameters components routes).2 huncovered⟩

noncomputable def executablePackagedAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.executablePackagedCoverageFormula components routes)

theorem eval_executablePackagedAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.executablePackagedAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (executablePackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [executablePackagedAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_executablePackagedCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_executablePackagedCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem
    eval_executablePackagedAllCoveredFormula_iff_not_existsUncovered
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ExecutablePackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.executablePackagedAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.executablePackagedExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_executablePackagedAllCoveredFormula_iff
      hnonempty components routes,
    family.eval_executablePackagedExistsUncoveredFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
