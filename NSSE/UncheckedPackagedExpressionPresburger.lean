import NSSE.UncheckedPackagedCapCoveragePresburger
import NSSE.PackagedFiniteAutomataPresburger

/-!
# Full unchecked packaged automata expressions

Cap components use arbitrary finite state types and require no right-language
nonemptiness proof.  Routes independently use arbitrary finite state types.
The compiler performs all reindexing, productivity, empty-component removal,
and state-count normalization internally.
-/

namespace NSSE

universe u v w

def PackagedDFARouteFamilyCovers
    (routes : List (PackagedFiniteDFA α))
    (word : Word α) : Prop :=
  ∃ route ∈ routes, ∃ position ≤ word.length,
    route.automaton.Accepts (word.take position)

theorem heterogeneousRouteFamily_of_packaged_iff
    (routes : List (PackagedFiniteDFA α))
    (word : Word α) :
    HeterogeneousDFARouteFamilyCovers
        (packagedRoutesToFinite routes) word ↔
      PackagedDFARouteFamilyCovers routes word := by
  induction routes with
  | nil =>
      simp [packagedRoutesToFinite,
        HeterogeneousDFARouteFamilyCovers,
        PackagedDFARouteFamilyCovers]
  | cons route routes ih =>
      unfold packagedRoutesToFinite at ih ⊢
      simp only [List.map_cons,
        HeterogeneousDFARouteFamilyCovers,
        PackagedDFARouteFamilyCovers, List.mem_cons]
      constructor
      · rintro (hroute | hroutes)
        · obtain ⟨position, hposition, haccepts⟩ := hroute
          change
            route.toFiniteDFA.automaton.language
              (word.take position) at haccepts
          rw [route.toFiniteDFA_language] at haccepts
          exact ⟨route, Or.inl rfl, position, hposition,
            haccepts⟩
        · obtain ⟨tailRoute, htailRoute, position,
              hposition, haccepts⟩ := ih.mp hroutes
          exact ⟨tailRoute, Or.inr htailRoute,
            position, hposition, haccepts⟩
      · rintro ⟨candidate, hcandidate, position,
          hposition, haccepts⟩
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          left
          refine ⟨position, hposition, ?_⟩
          change
            route.toFiniteDFA.automaton.language
              (word.take position)
          rw [route.toFiniteDFA_language]
          exact haccepts
        · exact Or.inr
            (ih.mpr ⟨candidate, hcandidate, position,
              hposition, haccepts⟩)

def UncheckedPackagedAutomataExpressionCovers
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α))
    (word : Word α) : Prop :=
  UncheckedPackagedCapFamilyCovers components word ∨
    PackagedDFARouteFamilyCovers routes word

def uncheckedPackagedAutomataCapExpression
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    CapExpression α where
  caps :=
    components.map UncheckedPackagedFiniteCapPair.capComponent
  routes := routes.map fun route => route.automaton.language

theorem uncheckedPackagedCapFamilyCovers_iff_capCovered
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α))
    (word : Word α) :
    UncheckedPackagedCapFamilyCovers components word ↔
      capCovered
        (uncheckedPackagedAutomataCapExpression
          components routes) word := by
  induction components with
  | nil =>
      simp [UncheckedPackagedCapFamilyCovers, capCovered,
        uncheckedPackagedAutomataCapExpression]
  | cons component components ih =>
      simp only [UncheckedPackagedCapFamilyCovers,
        uncheckedPackagedAutomataCapExpression,
        List.map_cons, capCovered, List.mem_cons]
      constructor
      · rintro (hcomponent | hcomponents)
        · exact ⟨component.capComponent,
            Or.inl rfl, hcomponent⟩
        · obtain ⟨covered, hcovered, hwitness⟩ :=
            ih.mp hcomponents
          exact ⟨covered, Or.inr hcovered, hwitness⟩
      · rintro ⟨covered, hcovered, hwitness⟩
        rcases hcovered with rfl | hcovered
        · exact Or.inl hwitness
        · exact Or.inr
            (ih.mpr ⟨covered, hcovered, hwitness⟩)

theorem packagedRouteFamilyCovers_iff_routeCovered
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α))
    (word : Word α) :
    PackagedDFARouteFamilyCovers routes word ↔
      routeCovered
        (uncheckedPackagedAutomataCapExpression
          components routes) word := by
  rw [routeCovered_iff_markedPrefix]
  constructor
  · rintro ⟨route, hroute, position, hposition, haccepts⟩
    exact ⟨route.automaton.language,
      List.mem_map.mpr ⟨route, hroute, rfl⟩,
      position, hposition, haccepts⟩
  · rintro ⟨language, hlanguage, position,
      hposition, haccepts⟩
    simp only [uncheckedPackagedAutomataCapExpression] at hlanguage
    obtain ⟨route, hroute, rfl⟩ := List.mem_map.mp hlanguage
    exact ⟨route, hroute, position, hposition, haccepts⟩

theorem uncheckedPackagedExpressionCovers_iff_covers
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α))
    (word : Word α) :
    UncheckedPackagedAutomataExpressionCovers
        components routes word ↔
      (uncheckedPackagedAutomataCapExpression
        components routes).Covers word := by
  unfold UncheckedPackagedAutomataExpressionCovers
    CapExpression.Covers
  rw [uncheckedPackagedCapFamilyCovers_iff_capCovered,
    packagedRouteFamilyCovers_iff_routeCovered]

namespace LinearWordFamily

noncomputable def uncheckedPackagedExpressionCoverageFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  .disj
    (family.uncheckedPackagedCapFamilyCoverageFormula components)
    (family.dfaRouteFamilyCoverageFormula
      (normalizeHeterogeneousDFARoutes
        (packagedRoutesToFinite routes)))

theorem eval_uncheckedPackagedExpressionCoverageFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.uncheckedPackagedExpressionCoverageFormula
      components routes).Eval parameters ↔
      UncheckedPackagedAutomataExpressionCovers
        components routes (family.word parameters) := by
  simp only [uncheckedPackagedExpressionCoverageFormula,
    NatPresburger.Eval,
    UncheckedPackagedAutomataExpressionCovers]
  rw [family.eval_uncheckedPackagedCapFamilyCoverageFormula_iff
      hnonempty parameters components,
    family.eval_dfaRouteFamilyCoverageFormula_iff
      hnonempty parameters
      (normalizeHeterogeneousDFARoutes
        (packagedRoutesToFinite routes)),
    dfaRouteFamilyCovers_normalizeHeterogeneous_iff,
    heterogeneousRouteFamily_of_packaged_iff]

theorem eval_uncheckedPackagedExpressionCoverageFormula_iff_covers
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.uncheckedPackagedExpressionCoverageFormula
      components routes).Eval parameters ↔
      (uncheckedPackagedAutomataCapExpression
        components routes).Covers (family.word parameters) := by
  rw [family.eval_uncheckedPackagedExpressionCoverageFormula_iff
      hnonempty parameters components routes,
    uncheckedPackagedExpressionCovers_iff_covers]

noncomputable def uncheckedPackagedExpressionUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger arity :=
  .neg
    (family.uncheckedPackagedExpressionCoverageFormula
      components routes)

theorem eval_uncheckedPackagedExpressionUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.uncheckedPackagedExpressionUncoveredFormula
      components routes).Eval parameters ↔
      (uncheckedPackagedAutomataCapExpression
        components routes).Uncovered (family.word parameters) := by
  rw [uncheckedPackagedExpressionUncoveredFormula,
    NatPresburger.Eval,
    family.eval_uncheckedPackagedExpressionCoverageFormula_iff_covers
      hnonempty parameters components routes]
  rfl

noncomputable def uncheckedPackagedExpressionExistsUncoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.uncheckedPackagedExpressionUncoveredFormula
      components routes)

theorem
    eval_uncheckedPackagedExpressionExistsUncoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.uncheckedPackagedExpressionExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [uncheckedPackagedExpressionExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_uncheckedPackagedExpressionUncoveredFormula_iff
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_uncheckedPackagedExpressionUncoveredFormula_iff
        hnonempty parameters components routes).2 huncovered⟩

noncomputable def uncheckedPackagedExpressionAllCoveredFormula
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.uncheckedPackagedExpressionCoverageFormula
      components routes)

theorem eval_uncheckedPackagedExpressionAllCoveredFormula_iff
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.uncheckedPackagedExpressionAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (uncheckedPackagedAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [uncheckedPackagedExpressionAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_uncheckedPackagedExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_uncheckedPackagedExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem
    eval_uncheckedPackagedExpressionAllCoveredFormula_iff_not_exists
    [Fintype α] [DecidableEq α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (UncheckedPackagedFiniteCapPair α))
    (routes : List (PackagedFiniteDFA α)) :
    (family.uncheckedPackagedExpressionAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.uncheckedPackagedExpressionExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_uncheckedPackagedExpressionAllCoveredFormula_iff
      hnonempty components routes,
    family.eval_uncheckedPackagedExpressionExistsUncoveredFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
