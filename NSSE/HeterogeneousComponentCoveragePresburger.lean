import NSSE.ComponentCoveragePresburger
import NSSE.HeterogeneousCapComponents
import NSSE.HeterogeneousDFARoutes

/-!
# Presburger coverage for heterogeneous component families

This is the public finite-component layer: individual retained components
may use different numbers of left and right states.  They are normalized to
the listwise maxima before invoking the homogeneous Presburger compiler.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

noncomputable def heterogeneousCapFamilyCoverageFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α)) :
    NatPresburger arity :=
  family.productiveCapFamilyCoverageFormula
    (normalizeHeterogeneousCapComponents components)

theorem eval_heterogeneousCapFamilyCoverageFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α)) :
    (family.heterogeneousCapFamilyCoverageFormula
      components).Eval parameters ↔
      HeterogeneousCapFamilyCovers components
        (family.word parameters) := by
  rw [heterogeneousCapFamilyCoverageFormula,
    family.eval_productiveCapFamilyCoverageFormula_iff
      hnonempty parameters
      (normalizeHeterogeneousCapComponents components),
    productiveCapFamilyCovers_normalizeHeterogeneous_iff]

def HeterogeneousAutomataExpressionCovers
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR))
    (word : Word α) : Prop :=
  HeterogeneousCapFamilyCovers components word ∨
    DFARouteFamilyCovers routes word

noncomputable def heterogeneousAutomataExpressionCoverageFormula
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    NatPresburger arity :=
  .disj
    (family.heterogeneousCapFamilyCoverageFormula components)
    (family.dfaRouteFamilyCoverageFormula routes)

theorem eval_heterogeneousAutomataExpressionCoverageFormula_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    (family.heterogeneousAutomataExpressionCoverageFormula
      components routes).Eval parameters ↔
      HeterogeneousAutomataExpressionCovers components routes
        (family.word parameters) := by
  simp only [heterogeneousAutomataExpressionCoverageFormula,
    NatPresburger.Eval, HeterogeneousAutomataExpressionCovers]
  rw [family.eval_heterogeneousCapFamilyCoverageFormula_iff
      hnonempty parameters components,
    family.eval_dfaRouteFamilyCoverageFormula_iff
      hnonempty parameters routes]

def heterogeneousAutomataCapExpression
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    CapExpression α where
  caps := components.map FiniteProductiveCapPair.capComponent
  routes := routes.map DFA.language

theorem heterogeneousCapFamilyCovers_iff_capCovered
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR))
    (word : Word α) :
    HeterogeneousCapFamilyCovers components word ↔
      capCovered
        (heterogeneousAutomataCapExpression components routes) word := by
  induction components with
  | nil =>
      simp [HeterogeneousCapFamilyCovers, capCovered,
        heterogeneousAutomataCapExpression]
  | cons component components ih =>
      simp only [HeterogeneousCapFamilyCovers,
        heterogeneousAutomataCapExpression, List.map_cons,
        capCovered, List.mem_cons]
      constructor
      · rintro (hcomponent | hcomponents)
        · exact ⟨component.capComponent, Or.inl rfl, hcomponent⟩
        · obtain ⟨covered, hcovered, hwitness⟩ :=
            ih.mp hcomponents
          exact ⟨covered, Or.inr hcovered, hwitness⟩
      · rintro ⟨covered, hcovered, hwitness⟩
        rcases hcovered with rfl | hcovered
        · exact Or.inl hwitness
        · exact Or.inr
            (ih.mpr ⟨covered, hcovered, hwitness⟩)

theorem heterogeneousDfaRouteFamilyCovers_iff_routeCovered
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR))
    (word : Word α) :
    DFARouteFamilyCovers routes word ↔
      routeCovered
        (heterogeneousAutomataCapExpression components routes) word := by
  rw [routeCovered_iff_markedPrefix]
  constructor
  · rintro ⟨route, hroute, position, hposition, haccepts⟩
    exact ⟨route.language,
      List.mem_map.mpr ⟨route, hroute, rfl⟩,
      position, hposition, haccepts⟩
  · rintro ⟨language, hlanguage, position, hposition, haccepts⟩
    simp only [heterogeneousAutomataCapExpression] at hlanguage
    obtain ⟨route, hroute, rfl⟩ := List.mem_map.mp hlanguage
    exact ⟨route, hroute, position, hposition, haccepts⟩

theorem heterogeneousAutomataExpressionCovers_iff_covers
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR))
    (word : Word α) :
    HeterogeneousAutomataExpressionCovers components routes word ↔
      (heterogeneousAutomataCapExpression
        components routes).Covers word := by
  unfold HeterogeneousAutomataExpressionCovers
    CapExpression.Covers
  rw [heterogeneousCapFamilyCovers_iff_capCovered,
    heterogeneousDfaRouteFamilyCovers_iff_routeCovered]

theorem
    eval_heterogeneousAutomataExpressionCoverageFormula_iff_covers
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    (family.heterogeneousAutomataExpressionCoverageFormula
      components routes).Eval parameters ↔
      (heterogeneousAutomataCapExpression
        components routes).Covers (family.word parameters) := by
  rw [family.eval_heterogeneousAutomataExpressionCoverageFormula_iff
      hnonempty parameters components routes,
    heterogeneousAutomataExpressionCovers_iff_covers]

noncomputable def
    heterogeneousAutomataExpressionUncoveredFormula
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    NatPresburger arity :=
  .neg
    (family.heterogeneousAutomataExpressionCoverageFormula
      components routes)

theorem
    eval_heterogeneousAutomataExpressionUncoveredFormula_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    (family.heterogeneousAutomataExpressionUncoveredFormula
      components routes).Eval parameters ↔
      (heterogeneousAutomataCapExpression
        components routes).Uncovered (family.word parameters) := by
  rw [heterogeneousAutomataExpressionUncoveredFormula,
    NatPresburger.Eval,
    family.eval_heterogeneousAutomataExpressionCoverageFormula_iff_covers
      hnonempty parameters components routes]
  rfl

noncomputable def heterogeneousExistsUncoveredParametersFormula
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.heterogeneousAutomataExpressionUncoveredFormula
      components routes)

theorem eval_heterogeneousExistsUncoveredParametersFormula_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    (family.heterogeneousExistsUncoveredParametersFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (heterogeneousAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [heterogeneousExistsUncoveredParametersFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_heterogeneousAutomataExpressionUncoveredFormula_iff
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_heterogeneousAutomataExpressionUncoveredFormula_iff
        hnonempty parameters components routes).2 huncovered⟩

noncomputable def heterogeneousAllParametersCoveredFormula
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.heterogeneousAutomataExpressionCoverageFormula
      components routes)

theorem eval_heterogeneousAllParametersCoveredFormula_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    (family.heterogeneousAllParametersCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (heterogeneousAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [heterogeneousAllParametersCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_heterogeneousAutomataExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_heterogeneousAutomataExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem
    eval_heterogeneousAllParametersCoveredFormula_iff_not_existsUncovered
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (DFA α QR)) :
    (family.heterogeneousAllParametersCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.heterogeneousExistsUncoveredParametersFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_heterogeneousAllParametersCoveredFormula_iff
      hnonempty components routes,
    family.eval_heterogeneousExistsUncoveredParametersFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

def FullyHeterogeneousAutomataExpressionCovers
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α))
    (word : Word α) : Prop :=
  HeterogeneousCapFamilyCovers components word ∨
    HeterogeneousDFARouteFamilyCovers routes word

noncomputable def fullyHeterogeneousExpressionCoverageFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    NatPresburger arity :=
  .disj
    (family.heterogeneousCapFamilyCoverageFormula components)
    (family.dfaRouteFamilyCoverageFormula
      (normalizeHeterogeneousDFARoutes routes))

theorem eval_fullyHeterogeneousExpressionCoverageFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    (family.fullyHeterogeneousExpressionCoverageFormula
      components routes).Eval parameters ↔
      FullyHeterogeneousAutomataExpressionCovers
        components routes (family.word parameters) := by
  simp only [fullyHeterogeneousExpressionCoverageFormula,
    NatPresburger.Eval,
    FullyHeterogeneousAutomataExpressionCovers]
  rw [family.eval_heterogeneousCapFamilyCoverageFormula_iff
      hnonempty parameters components,
    family.eval_dfaRouteFamilyCoverageFormula_iff
      hnonempty parameters
      (normalizeHeterogeneousDFARoutes routes),
    dfaRouteFamilyCovers_normalizeHeterogeneous_iff]

def fullyHeterogeneousAutomataCapExpression
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    CapExpression α where
  caps := components.map FiniteProductiveCapPair.capComponent
  routes := routes.map fun route => route.automaton.language

theorem fullyHeterogeneousCapFamilyCovers_iff_capCovered
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α))
    (word : Word α) :
    HeterogeneousCapFamilyCovers components word ↔
      capCovered
        (fullyHeterogeneousAutomataCapExpression
          components routes) word := by
  induction components with
  | nil =>
      simp [HeterogeneousCapFamilyCovers, capCovered,
        fullyHeterogeneousAutomataCapExpression]
  | cons component components ih =>
      simp only [HeterogeneousCapFamilyCovers,
        fullyHeterogeneousAutomataCapExpression, List.map_cons,
        capCovered, List.mem_cons]
      constructor
      · rintro (hcomponent | hcomponents)
        · exact ⟨component.capComponent, Or.inl rfl, hcomponent⟩
        · obtain ⟨covered, hcovered, hwitness⟩ :=
            ih.mp hcomponents
          exact ⟨covered, Or.inr hcovered, hwitness⟩
      · rintro ⟨covered, hcovered, hwitness⟩
        rcases hcovered with rfl | hcovered
        · exact Or.inl hwitness
        · exact Or.inr
            (ih.mpr ⟨covered, hcovered, hwitness⟩)

theorem fullyHeterogeneousRouteFamilyCovers_iff_routeCovered
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α))
    (word : Word α) :
    HeterogeneousDFARouteFamilyCovers routes word ↔
      routeCovered
        (fullyHeterogeneousAutomataCapExpression
          components routes) word := by
  rw [routeCovered_iff_markedPrefix]
  induction routes with
  | nil =>
      simp [HeterogeneousDFARouteFamilyCovers,
        fullyHeterogeneousAutomataCapExpression]
  | cons route routes ih =>
      simp only [HeterogeneousDFARouteFamilyCovers,
        fullyHeterogeneousAutomataCapExpression, List.map_cons,
        List.mem_cons]
      constructor
      · rintro (hroute | hroutes)
        · obtain ⟨position, hposition, haccepts⟩ := hroute
          exact ⟨route.automaton.language, Or.inl rfl,
            position, hposition, haccepts⟩
        · obtain ⟨language, hlanguage, position,
              hposition, haccepts⟩ := ih.mp hroutes
          exact ⟨language, Or.inr hlanguage,
            position, hposition, haccepts⟩
      · rintro ⟨language, hlanguage, position,
          hposition, haccepts⟩
        rcases hlanguage with rfl | hlanguage
        · exact Or.inl ⟨position, hposition, haccepts⟩
        · exact Or.inr
            (ih.mpr ⟨language, hlanguage, position,
              hposition, haccepts⟩)

theorem fullyHeterogeneousExpressionCovers_iff_covers
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α))
    (word : Word α) :
    FullyHeterogeneousAutomataExpressionCovers
        components routes word ↔
      (fullyHeterogeneousAutomataCapExpression
        components routes).Covers word := by
  unfold FullyHeterogeneousAutomataExpressionCovers
    CapExpression.Covers
  rw [fullyHeterogeneousCapFamilyCovers_iff_capCovered,
    fullyHeterogeneousRouteFamilyCovers_iff_routeCovered]

theorem eval_fullyHeterogeneousExpressionCoverageFormula_iff_covers
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    (family.fullyHeterogeneousExpressionCoverageFormula
      components routes).Eval parameters ↔
      (fullyHeterogeneousAutomataCapExpression
        components routes).Covers (family.word parameters) := by
  rw [family.eval_fullyHeterogeneousExpressionCoverageFormula_iff
      hnonempty parameters components routes,
    fullyHeterogeneousExpressionCovers_iff_covers]

noncomputable def fullyHeterogeneousUncoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    NatPresburger arity :=
  .neg
    (family.fullyHeterogeneousExpressionCoverageFormula
      components routes)

theorem eval_fullyHeterogeneousUncoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    (family.fullyHeterogeneousUncoveredFormula
      components routes).Eval parameters ↔
      (fullyHeterogeneousAutomataCapExpression
        components routes).Uncovered (family.word parameters) := by
  rw [fullyHeterogeneousUncoveredFormula,
    NatPresburger.Eval,
    family.eval_fullyHeterogeneousExpressionCoverageFormula_iff_covers
      hnonempty parameters components routes]
  rfl

noncomputable def fullyHeterogeneousExistsUncoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.fullyHeterogeneousUncoveredFormula
      components routes)

theorem eval_fullyHeterogeneousExistsUncoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    (family.fullyHeterogeneousExistsUncoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (fullyHeterogeneousAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [fullyHeterogeneousExistsUncoveredFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_fullyHeterogeneousUncoveredFormula_iff
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_fullyHeterogeneousUncoveredFormula_iff
        hnonempty parameters components routes).2 huncovered⟩

noncomputable def fullyHeterogeneousAllCoveredFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.fullyHeterogeneousExpressionCoverageFormula
      components routes)

theorem eval_fullyHeterogeneousAllCoveredFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    (family.fullyHeterogeneousAllCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (fullyHeterogeneousAutomataCapExpression
          components routes).Covers
            (family.word parameters) := by
  rw [fullyHeterogeneousAllCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_fullyHeterogeneousExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_fullyHeterogeneousExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem
    eval_fullyHeterogeneousAllCoveredFormula_iff_not_existsUncovered
    [Fintype α]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (FiniteProductiveCapPair α))
    (routes : List (FiniteDFA α)) :
    (family.fullyHeterogeneousAllCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.fullyHeterogeneousExistsUncoveredFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_fullyHeterogeneousAllCoveredFormula_iff
      hnonempty components routes,
    family.eval_fullyHeterogeneousExistsUncoveredFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

end LinearWordFamily

end NSSE
