import NSSE.HeterogeneousComponentCoveragePresburger
import NSSE.ClassicalProductivity

/-!
# Presburger compilation from arbitrary finite state types

The public package stores each automaton together with its own finite state
type and `Fintype` certificate.  Reindexing to `Fin (card Q)` is internal.
Thus neither common state types nor explicit `Fin` presentations are required
at the input boundary.
-/

namespace NSSE

universe u v w

structure PackagedFiniteDFA (α : Type u) where
  State : Type v
  stateFintype : Fintype State
  automaton : DFA α State

namespace PackagedFiniteDFA

noncomputable def toFiniteDFA
    (route : PackagedFiniteDFA α) : FiniteDFA α := by
  letI : Fintype route.State := route.stateFintype
  exact
    { stateCount := Fintype.card route.State
      automaton := route.automaton.finReindex }

theorem toFiniteDFA_language
    (route : PackagedFiniteDFA α) :
    route.toFiniteDFA.automaton.language =
      route.automaton.language := by
  letI : Fintype route.State := route.stateFintype
  exact route.automaton.finReindex_language

end PackagedFiniteDFA

structure PackagedFiniteCapPair (α : Type u) where
  LeftState : Type v
  RightState : Type w
  leftFintype : Fintype LeftState
  rightFintype : Fintype RightState
  left : DFA α LeftState
  right : DFA α RightState
  right_nonempty : ∃ word, right.language word

structure PackagedFiniteProductiveCapPair (α : Type u) where
  LeftState : Type v
  RightState : Type w
  leftFintype : Fintype LeftState
  rightFintype : Fintype RightState
  left : ProductiveDFA α LeftState
  right : ProductiveDFA α RightState
  right_nonempty : ∃ word, right.language word

namespace PackagedFiniteProductiveCapPair

def capComponent
    (component : PackagedFiniteProductiveCapPair α) :
    CapComponent α :=
  automataCapComponent component.left component.right

noncomputable def toFiniteProductiveCapPair
    (component : PackagedFiniteProductiveCapPair α) :
    FiniteProductiveCapPair α := by
  letI : Fintype component.LeftState := component.leftFintype
  letI : Fintype component.RightState := component.rightFintype
  exact
    { leftCount := Fintype.card component.LeftState
      rightCount := Fintype.card component.RightState
      left := component.left.finReindex
      right := component.right.finReindex
      right_nonempty := by
        rw [component.right.finReindex_language]
        exact component.right_nonempty }

@[simp] theorem toFiniteProductiveCapPair_capComponent
    (component : PackagedFiniteProductiveCapPair α) :
    component.toFiniteProductiveCapPair.capComponent =
      component.capComponent := by
  letI : Fintype component.LeftState := component.leftFintype
  letI : Fintype component.RightState := component.rightFintype
  exact automataCapComponent_finReindex
    component.left component.right

end PackagedFiniteProductiveCapPair

namespace PackagedFiniteCapPair

def capComponent (component : PackagedFiniteCapPair α) :
    CapComponent α :=
  CapComponent.ofDFA component.left component.right

noncomputable def certifyProductivity
    (component : PackagedFiniteCapPair α) :
    PackagedFiniteProductiveCapPair α where
  LeftState := component.LeftState
  RightState := component.RightState
  leftFintype := component.leftFintype
  rightFintype := component.rightFintype
  left := component.left.classicalProductive
  right := component.right.classicalProductive
  right_nonempty := by
    rw [component.right.classicalProductive_language]
    exact component.right_nonempty

@[simp] theorem certifyProductivity_capComponent
    (component : PackagedFiniteCapPair α) :
    component.certifyProductivity.capComponent =
      component.capComponent :=
  rfl

end PackagedFiniteCapPair

def packagedFiniteAutomataCapExpression
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    CapExpression α where
  caps :=
    components.map
      PackagedFiniteProductiveCapPair.capComponent
  routes := routes.map fun route => route.automaton.language

noncomputable def packagedComponentsToFinite
    (components : List (PackagedFiniteProductiveCapPair α)) :
    List (FiniteProductiveCapPair α) :=
  components.map
    PackagedFiniteProductiveCapPair.toFiniteProductiveCapPair

noncomputable def packagedRoutesToFinite
    (routes : List (PackagedFiniteDFA α)) :
    List (FiniteDFA α) :=
  routes.map PackagedFiniteDFA.toFiniteDFA

theorem fullyHeterogeneousExpression_of_packaged_eq
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    LinearWordFamily.fullyHeterogeneousAutomataCapExpression
        (packagedComponentsToFinite components)
        (packagedRoutesToFinite routes) =
      packagedFiniteAutomataCapExpression components routes := by
  unfold LinearWordFamily.fullyHeterogeneousAutomataCapExpression
    packagedFiniteAutomataCapExpression
    packagedComponentsToFinite packagedRoutesToFinite
  rw [List.map_map, List.map_map]
  have hcomponents :
      (fun component : PackagedFiniteProductiveCapPair α =>
        component.toFiniteProductiveCapPair.capComponent) =
      (fun component : PackagedFiniteProductiveCapPair α =>
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

noncomputable def packagedFiniteExpressionCoverageFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  family.fullyHeterogeneousExpressionCoverageFormula
    (packagedComponentsToFinite components)
    (packagedRoutesToFinite routes)

theorem eval_packagedFiniteExpressionCoverageFormula_iff_covers
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.packagedFiniteExpressionCoverageFormula
      components routes).Eval parameters ↔
      (packagedFiniteAutomataCapExpression
        components routes).Covers (family.word parameters) := by
  rw [packagedFiniteExpressionCoverageFormula,
    family.eval_fullyHeterogeneousExpressionCoverageFormula_iff_covers
      hnonempty parameters
      (packagedComponentsToFinite components)
      (packagedRoutesToFinite routes),
    fullyHeterogeneousExpression_of_packaged_eq]

noncomputable def packagedFiniteUncoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  .neg (family.packagedFiniteExpressionCoverageFormula
    components routes)

theorem eval_packagedFiniteUncoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.packagedFiniteUncoveredFormula
      components routes).Eval parameters ↔
      (packagedFiniteAutomataCapExpression
        components routes).Uncovered (family.word parameters) := by
  rw [packagedFiniteUncoveredFormula, NatPresburger.Eval,
    family.eval_packagedFiniteExpressionCoverageFormula_iff_covers
      hnonempty parameters components routes]
  rfl

noncomputable def packagedFiniteExistsUncoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.packagedFiniteUncoveredFormula components routes)

theorem eval_packagedFiniteExistsUncoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.packagedFiniteExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (packagedFiniteAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [packagedFiniteExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_packagedFiniteUncoveredFormula_iff
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_packagedFiniteUncoveredFormula_iff
        hnonempty parameters components routes).2 huncovered⟩

noncomputable def packagedFiniteAllCoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.packagedFiniteExpressionCoverageFormula components routes)

theorem eval_packagedFiniteAllCoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.packagedFiniteAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (packagedFiniteAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [packagedFiniteAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_packagedFiniteExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_packagedFiniteExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem
    eval_packagedFiniteAllCoveredFormula_iff_not_existsUncovered
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (PackagedFiniteProductiveCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.packagedFiniteAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.packagedFiniteExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_packagedFiniteAllCoveredFormula_iff
      hnonempty components routes,
    family.eval_packagedFiniteExistsUncoveredFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

noncomputable def rawPackagedComponentsToProductive
    (components : List (PackagedFiniteCapPair α)) :
    List (PackagedFiniteProductiveCapPair α) :=
  components.map PackagedFiniteCapPair.certifyProductivity

def rawPackagedFiniteAutomataCapExpression
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    CapExpression α where
  caps := components.map PackagedFiniteCapPair.capComponent
  routes := routes.map fun route => route.automaton.language

theorem packagedProductiveExpression_of_raw_eq
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    packagedFiniteAutomataCapExpression
        (rawPackagedComponentsToProductive components) routes =
      rawPackagedFiniteAutomataCapExpression components routes := by
  unfold packagedFiniteAutomataCapExpression
    rawPackagedFiniteAutomataCapExpression
    rawPackagedComponentsToProductive
  rw [List.map_map]
  have hcomponents :
      (fun component : PackagedFiniteCapPair α =>
        component.certifyProductivity.capComponent) =
      (fun component : PackagedFiniteCapPair α =>
        component.capComponent) := by
    funext component
    exact component.certifyProductivity_capComponent
  simp only [Function.comp_def]
  rw [hcomponents]

namespace LinearWordFamily

noncomputable def rawPackagedFiniteExpressionCoverageFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  family.packagedFiniteExpressionCoverageFormula
    (rawPackagedComponentsToProductive components) routes

theorem eval_rawPackagedFiniteExpressionCoverageFormula_iff_covers
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.rawPackagedFiniteExpressionCoverageFormula
      components routes).Eval parameters ↔
      (rawPackagedFiniteAutomataCapExpression
        components routes).Covers (family.word parameters) := by
  rw [rawPackagedFiniteExpressionCoverageFormula,
    family.eval_packagedFiniteExpressionCoverageFormula_iff_covers
      hnonempty parameters
      (rawPackagedComponentsToProductive components) routes,
    packagedProductiveExpression_of_raw_eq]

noncomputable def rawPackagedFiniteUncoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  .neg (family.rawPackagedFiniteExpressionCoverageFormula
    components routes)

theorem eval_rawPackagedFiniteUncoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.rawPackagedFiniteUncoveredFormula
      components routes).Eval parameters ↔
      (rawPackagedFiniteAutomataCapExpression
        components routes).Uncovered (family.word parameters) := by
  rw [rawPackagedFiniteUncoveredFormula, NatPresburger.Eval,
    family.eval_rawPackagedFiniteExpressionCoverageFormula_iff_covers
      hnonempty parameters components routes]
  rfl

noncomputable def rawPackagedFiniteExistsUncoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.rawPackagedFiniteUncoveredFormula components routes)

theorem eval_rawPackagedFiniteExistsUncoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.rawPackagedFiniteExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (rawPackagedFiniteAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [rawPackagedFiniteExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_rawPackagedFiniteUncoveredFormula_iff
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_rawPackagedFiniteUncoveredFormula_iff
        hnonempty parameters components routes).2 huncovered⟩

noncomputable def rawPackagedFiniteAllCoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.rawPackagedFiniteExpressionCoverageFormula components routes)

theorem eval_rawPackagedFiniteAllCoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.rawPackagedFiniteAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (rawPackagedFiniteAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [rawPackagedFiniteAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_rawPackagedFiniteExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_rawPackagedFiniteExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem
    eval_rawPackagedFiniteAllCoveredFormula_iff_not_existsUncovered
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (PackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.rawPackagedFiniteAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.rawPackagedFiniteExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_rawPackagedFiniteAllCoveredFormula_iff
      hnonempty components routes,
    family.eval_rawPackagedFiniteExistsUncoveredFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
