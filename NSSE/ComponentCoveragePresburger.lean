import NSSE.AllPeriodicWitnessesPresburger
import NSSE.DFAReindexing
import NSSE.DFAPadding

/-!
# Presburger compilation of one cap component
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def componentCoverageFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  .disj
    (family.componentRoutesFormula left right)
    (family.allPeriodicWitnessesFormula
      left.automaton right.automaton)

theorem eval_componentCoverageFormula_iff_normalForm
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.componentCoverageFormula left right).Eval parameters ↔
      ComponentNormalForm (automataCapComponent left right)
        (family.word parameters) := by
  simp only [componentCoverageFormula, NatPresburger.Eval,
    ComponentNormalForm]
  rw [family.eval_componentRoutesFormula_iff
      left right hnonempty parameters,
    family.eval_allPeriodicWitnessesFormula_iff_periodicWitness
      left right hnonempty parameters]
  tauto

theorem eval_componentCoverageFormula_iff_capComponentCovers
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (hrightNonempty :
      ∃ word, right.automaton.Accepts word)
    (parameters : Fin arity → Nat) :
    (family.componentCoverageFormula left right).Eval parameters ↔
      capComponentCovers (automataCapComponent left right)
        (family.word parameters) := by
  rw [family.eval_componentCoverageFormula_iff_normalForm
      left right hnonempty parameters]
  symm
  apply capComponentCovers_iff_componentNormalForm
  simpa [automataCapComponent, ProductiveDFA.language,
    DFA.language] using hrightNonempty

theorem eval_componentCoverageFormula_reindex_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    [Fintype R₁] [Fintype R₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (leftEquiv : Equiv Q₁ R₁) (rightEquiv : Equiv Q₂ R₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (hrightNonempty : ∃ word, right.automaton.Accepts word)
    (parameters : Fin arity → Nat) :
    (family.componentCoverageFormula
        (left.reindex leftEquiv)
        (right.reindex rightEquiv)).Eval parameters ↔
      (family.componentCoverageFormula left right).Eval parameters := by
  have hreindexedRightNonempty :
      ∃ word,
        (right.reindex rightEquiv).automaton.Accepts word := by
    obtain ⟨word, haccepts⟩ := hrightNonempty
    exact ⟨word,
      (right.automaton.reindex_accepts
        rightEquiv word).2 haccepts⟩
  rw [family.eval_componentCoverageFormula_iff_capComponentCovers
      (left.reindex leftEquiv) (right.reindex rightEquiv)
      hnonempty hreindexedRightNonempty parameters,
    family.eval_componentCoverageFormula_iff_capComponentCovers
      left right hnonempty hrightNonempty parameters,
    automataCapComponent_reindex]

theorem eval_componentCoverageFormula_finPad_iff
    [Fintype α]
    (left : ProductiveDFA α (Fin n₁))
    (right : ProductiveDFA α (Fin n₂))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (hrightNonempty : ∃ word, right.automaton.Accepts word)
    (parameters : Fin arity → Nat) :
    (family.componentCoverageFormula
        (left.finPad hleft)
        (right.finPad hright)).Eval parameters ↔
      (family.componentCoverageFormula left right).Eval parameters := by
  have hpaddedRightNonempty :
      ∃ word, (right.finPad hright).automaton.Accepts word := by
    obtain ⟨word, haccepts⟩ := hrightNonempty
    exact ⟨word,
      (right.automaton.finPad_accepts hright word).2 haccepts⟩
  rw [family.eval_componentCoverageFormula_iff_capComponentCovers
      (left.finPad hleft) (right.finPad hright)
      hnonempty hpaddedRightNonempty parameters,
    family.eval_componentCoverageFormula_iff_capComponentCovers
      left right hnonempty hrightNonempty parameters,
    automataCapComponent_finPad]

noncomputable def productiveCapFamilyCoverageFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (family : LinearWordFamily α arity)
    (components : List (ProductiveCapPair α Q₁ Q₂)) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    components.map fun component =>
      family.componentCoverageFormula
        component.left component.right

theorem eval_productiveCapFamilyCoverageFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ProductiveCapPair α Q₁ Q₂)) :
    (family.productiveCapFamilyCoverageFormula
      components).Eval parameters ↔
      ProductiveCapFamilyCovers components
        (family.word parameters) := by
  induction components with
  | nil =>
      simp [productiveCapFamilyCoverageFormula,
        NatPresburger.disjoin, ProductiveCapFamilyCovers,
        NatPresburger.Eval]
  | cons component components ih =>
      rw [productiveCapFamilyCoverageFormula,
        List.map_cons, NatPresburger.disjoin,
        NatPresburger.Eval]
      rw [family.eval_componentCoverageFormula_iff_capComponentCovers
        component.left component.right hnonempty
        (by
          simpa [ProductiveDFA.language, DFA.language] using
            component.right_nonempty)
        parameters]
      change
        capComponentCovers
              (automataCapComponent component.left component.right)
              (family.word parameters) ∨
            (family.productiveCapFamilyCoverageFormula
              components).Eval parameters ↔
          ProductiveCapFamilyCovers (component :: components)
            (family.word parameters)
      rw [ih]
      rfl

noncomputable def dfaAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  Classical.choose (family.dfaAcceptance_presburger automaton)

theorem eval_dfaAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    (family.dfaAcceptanceFormula automaton).Eval parameters ↔
      automaton.Accepts (family.word parameters) :=
  Classical.choose_spec
    (family.dfaAcceptance_presburger automaton) parameters

def DFAFamilyCovers
    (routes : List (DFA α Q))
    (word : Word α) : Prop :=
  ∃ route ∈ routes, route.Accepts word

noncomputable def dfaFamilyCoverageFormula
    [Fintype Q]
    (family : LinearWordFamily α arity)
    (routes : List (DFA α Q)) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    routes.map family.dfaAcceptanceFormula

theorem eval_dfaFamilyCoverageFormula_iff
    [Fintype Q]
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (routes : List (DFA α Q)) :
    (family.dfaFamilyCoverageFormula routes).Eval parameters ↔
      DFAFamilyCovers routes (family.word parameters) := by
  rw [dfaFamilyCoverageFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map] at hformula
    obtain ⟨route, hroute, rfl⟩ := hformula
    exact ⟨route, hroute,
      (family.eval_dfaAcceptanceFormula_iff
        route parameters).1 heval⟩
  · rintro ⟨route, hroute, haccepts⟩
    refine ⟨family.dfaAcceptanceFormula route,
      List.mem_map.mpr ⟨route, hroute, rfl⟩, ?_⟩
    exact
      (family.eval_dfaAcceptanceFormula_iff
        route parameters).2 haccepts

def ProductiveRouteFamilyCovers
    (routes : List (ProductiveDFA α Q))
    (word : Word α) : Prop :=
  ∃ route ∈ routes,
    Language.prefixClosure route.language word

noncomputable def productiveRouteFamilyCoverageFormula
    [Fintype Q]
    (family : LinearWordFamily α arity)
    (routes : List (ProductiveDFA α Q)) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    routes.map fun route => family.prefixRouteFormula route

theorem eval_productiveRouteFamilyCoverageFormula_iff
    [Fintype Q]
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (routes : List (ProductiveDFA α Q)) :
    (family.productiveRouteFamilyCoverageFormula
      routes).Eval parameters ↔
      ProductiveRouteFamilyCovers routes
        (family.word parameters) := by
  rw [productiveRouteFamilyCoverageFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map] at hformula
    obtain ⟨route, hroute, rfl⟩ := hformula
    refine ⟨route, hroute, ?_⟩
    rw [prefixRouteFormula,
      NatPresburger.poweredStatePredicateFormula_correct,
      family.evaluate_dfaStages] at heval
    exact (route.prefixClosure_iff
      (family.word parameters)).2 heval
  · rintro ⟨route, hroute, haccepts⟩
    refine ⟨family.prefixRouteFormula route,
      List.mem_map.mpr ⟨route, hroute, rfl⟩, ?_⟩
    rw [prefixRouteFormula,
      NatPresburger.poweredStatePredicateFormula_correct,
      family.evaluate_dfaStages]
    exact (route.prefixClosure_iff
      (family.word parameters)).1 haccepts

noncomputable def dfaRouteCoverageFormula
    [Fintype Q]
    (route : DFA α Q)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    family.allAddressedCutCases.map
      (family.addressedCutPrefixStatePredicateFormula
        route route.accept)

theorem eval_dfaRouteCoverageFormula_iff
    [Fintype Q]
    (route : DFA α Q)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.dfaRouteCoverageFormula route).Eval parameters ↔
      ∃ position ≤ (family.word parameters).length,
        route.Accepts
          ((family.word parameters).take position) := by
  rw [dfaRouteCoverageFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map] at hformula
    obtain ⟨cut, hcut, rfl⟩ := hformula
    obtain ⟨copy, hvalid, haccepts⟩ :=
      (family.eval_addressedCutPrefixStatePredicateFormula_iff
        route parameters route.accept cut).1 heval
    let position :=
      family.addressedCutPosition parameters cut copy
    refine ⟨position,
      family.addressedCutPosition_le_word_length
        parameters cut copy hvalid, ?_⟩
    have htake :=
      family.take_word_eq_addressedCutPrefix
        parameters cut copy hvalid
    rw [htake]
    exact haccepts
  · rintro ⟨position, hposition, haccepts⟩
    obtain ⟨cut, hcut, copy, hvalid, hpositionEq⟩ :=
      family.exists_addressedCut_at_position
        hnonempty parameters position hposition
    refine ⟨family.addressedCutPrefixStatePredicateFormula
      route route.accept cut,
      List.mem_map.mpr ⟨cut, hcut, rfl⟩, ?_⟩
    apply
      (family.eval_addressedCutPrefixStatePredicateFormula_iff
        route parameters route.accept cut).2
    refine ⟨copy, hvalid, ?_⟩
    have htake :=
      family.take_word_eq_addressedCutPrefix
        parameters cut copy hvalid
    rw [← htake, hpositionEq]
    exact haccepts

def DFARouteFamilyCovers
    (routes : List (DFA α Q))
    (word : Word α) : Prop :=
  ∃ route ∈ routes, ∃ position ≤ word.length,
    route.Accepts (word.take position)

noncomputable def dfaRouteFamilyCoverageFormula
    [Fintype Q]
    (family : LinearWordFamily α arity)
    (routes : List (DFA α Q)) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    routes.map family.dfaRouteCoverageFormula

theorem eval_dfaRouteFamilyCoverageFormula_iff
    [Fintype Q]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (routes : List (DFA α Q)) :
    (family.dfaRouteFamilyCoverageFormula routes).Eval parameters ↔
      DFARouteFamilyCovers routes
        (family.word parameters) := by
  rw [dfaRouteFamilyCoverageFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map] at hformula
    obtain ⟨route, hroute, rfl⟩ := hformula
    exact ⟨route, hroute,
      (family.eval_dfaRouteCoverageFormula_iff
        route hnonempty parameters).1 heval⟩
  · rintro ⟨route, hroute, hcovered⟩
    exact ⟨family.dfaRouteCoverageFormula route,
      List.mem_map.mpr ⟨route, hroute, rfl⟩,
      (family.eval_dfaRouteCoverageFormula_iff
        route hnonempty parameters).2 hcovered⟩

def ProductiveAutomataExpressionCovers
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR))
    (word : Word α) : Prop :=
  ProductiveCapFamilyCovers components word ∨
    DFARouteFamilyCovers routes word

noncomputable def productiveAutomataExpressionCoverageFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    NatPresburger arity :=
  .disj
    (family.productiveCapFamilyCoverageFormula components)
    (family.dfaRouteFamilyCoverageFormula routes)

theorem eval_productiveAutomataExpressionCoverageFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.productiveAutomataExpressionCoverageFormula
      components routes).Eval parameters ↔
      ProductiveAutomataExpressionCovers components routes
        (family.word parameters) := by
  simp only [productiveAutomataExpressionCoverageFormula,
    ProductiveAutomataExpressionCovers, NatPresburger.Eval]
  rw [family.eval_productiveCapFamilyCoverageFormula_iff
      hnonempty parameters components,
    family.eval_dfaRouteFamilyCoverageFormula_iff
      hnonempty parameters routes]

noncomputable def productiveAutomataExpressionUncoveredFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    NatPresburger arity :=
  .neg
    (family.productiveAutomataExpressionCoverageFormula
      components routes)

theorem eval_productiveAutomataExpressionUncoveredFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.productiveAutomataExpressionUncoveredFormula
      components routes).Eval parameters ↔
      ¬ ProductiveAutomataExpressionCovers components routes
        (family.word parameters) := by
  rw [productiveAutomataExpressionUncoveredFormula,
    NatPresburger.Eval,
    family.eval_productiveAutomataExpressionCoverageFormula_iff
      hnonempty parameters components routes]

def productiveAutomataCapExpression
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    CapExpression α where
  caps :=
    components.map fun component =>
      automataCapComponent component.left component.right
  routes := routes.map DFA.language

theorem productiveCapFamilyCovers_iff_capCovered
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR))
    (word : Word α) :
    ProductiveCapFamilyCovers components word ↔
      capCovered
        (productiveAutomataCapExpression components routes) word := by
  induction components with
  | nil =>
      simp [ProductiveCapFamilyCovers, capCovered,
        productiveAutomataCapExpression]
  | cons component components ih =>
      simp only [ProductiveCapFamilyCovers,
        productiveAutomataCapExpression, List.map_cons, capCovered,
        List.mem_cons]
      constructor
      · rintro (hcomponent | hcomponents)
        · exact ⟨automataCapComponent component.left component.right,
            Or.inl rfl, hcomponent⟩
        · obtain ⟨covered, hcovered, hwitness⟩ := ih.mp hcomponents
          exact ⟨covered, Or.inr hcovered, hwitness⟩
      · rintro ⟨covered, hcovered, hwitness⟩
        rcases hcovered with rfl | hcovered
        · exact Or.inl hwitness
        · exact Or.inr (ih.mpr ⟨covered, hcovered, hwitness⟩)

theorem dfaRouteFamilyCovers_iff_routeCovered
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR))
    (word : Word α) :
    DFARouteFamilyCovers routes word ↔
      routeCovered
        (productiveAutomataCapExpression components routes) word := by
  rw [routeCovered_iff_markedPrefix]
  constructor
  · rintro ⟨route, hroute, position, hposition, haccepts⟩
    exact ⟨route.language,
      List.mem_map.mpr ⟨route, hroute, rfl⟩,
      position, hposition, haccepts⟩
  · rintro ⟨language, hlanguage, position, hposition, haccepts⟩
    simp only [productiveAutomataCapExpression] at hlanguage
    obtain ⟨route, hroute, rfl⟩ := List.mem_map.mp hlanguage
    exact ⟨route, hroute, position, hposition, haccepts⟩

theorem productiveAutomataExpressionCovers_iff_capExpressionCovers
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR))
    (word : Word α) :
    ProductiveAutomataExpressionCovers components routes word ↔
      (productiveAutomataCapExpression components routes).Covers word := by
  unfold ProductiveAutomataExpressionCovers CapExpression.Covers
  rw [productiveCapFamilyCovers_iff_capCovered,
    dfaRouteFamilyCovers_iff_routeCovered]

theorem productiveAutomataCapExpression_finPad
    (components :
      List (ProductiveCapPair α (Fin n₁) (Fin n₂)))
    (routes : List (DFA α QR))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    productiveAutomataCapExpression
        (components.map fun component =>
          component.finPad hleft hright) routes =
      productiveAutomataCapExpression components routes := by
  unfold productiveAutomataCapExpression
  rw [List.map_map]
  have hcomponent :
      (fun component : ProductiveCapPair α (Fin n₁) (Fin n₂) =>
        automataCapComponent
          (component.finPad hleft hright).left
          (component.finPad hleft hright).right) =
        (fun component =>
          automataCapComponent component.left component.right) := by
    funext component
    exact component.finPad_capComponent hleft hright
  simp only [Function.comp_def]
  rw [hcomponent]

theorem eval_productiveAutomataExpressionCoverageFormula_iff_covers
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.productiveAutomataExpressionCoverageFormula
      components routes).Eval parameters ↔
      (productiveAutomataCapExpression components routes).Covers
        (family.word parameters) := by
  rw [family.eval_productiveAutomataExpressionCoverageFormula_iff
      hnonempty parameters components routes,
    productiveAutomataExpressionCovers_iff_capExpressionCovers]

theorem
    eval_productiveAutomataExpressionCoverageFormula_finPad_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components :
      List (ProductiveCapPair α (Fin n₁) (Fin n₂)))
    (routes : List (DFA α QR))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    (family.productiveAutomataExpressionCoverageFormula
        (components.map fun component =>
          component.finPad hleft hright) routes).Eval parameters ↔
      (family.productiveAutomataExpressionCoverageFormula
        components routes).Eval parameters := by
  rw [family.eval_productiveAutomataExpressionCoverageFormula_iff_covers
      hnonempty parameters
      (components.map fun component =>
        component.finPad hleft hright) routes,
    family.eval_productiveAutomataExpressionCoverageFormula_iff_covers
      hnonempty parameters components routes,
    productiveAutomataCapExpression_finPad]

theorem eval_productiveAutomataExpressionUncoveredFormula_iff_uncovered
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.productiveAutomataExpressionUncoveredFormula
      components routes).Eval parameters ↔
      (productiveAutomataCapExpression components routes).Uncovered
        (family.word parameters) := by
  rw [family.eval_productiveAutomataExpressionUncoveredFormula_iff
      hnonempty parameters components routes]
  unfold CapExpression.Uncovered
  rw [productiveAutomataExpressionCovers_iff_capExpressionCovers]

noncomputable def existsUncoveredParametersFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    NatPresburger 0 :=
  NatPresburger.existentialClosure arity
    (family.productiveAutomataExpressionUncoveredFormula
      components routes)

theorem eval_existsUncoveredParametersFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.existsUncoveredParametersFormula
      components routes).Eval Fin.elim0 ↔
      ∃ parameters : Fin arity → Nat,
        (productiveAutomataCapExpression
          components routes).Uncovered
            (family.word parameters) := by
  rw [existsUncoveredParametersFormula,
    NatPresburger.eval_existentialClosure_iff]
  constructor
  · rintro ⟨parameters, heval⟩
    exact ⟨parameters,
      (family.eval_productiveAutomataExpressionUncoveredFormula_iff_uncovered
        hnonempty parameters components routes).1 heval⟩
  · rintro ⟨parameters, huncovered⟩
    exact ⟨parameters,
      (family.eval_productiveAutomataExpressionUncoveredFormula_iff_uncovered
        hnonempty parameters components routes).2 huncovered⟩

theorem not_eval_existsUncoveredParametersFormula_iff_all_covered
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    ¬ (family.existsUncoveredParametersFormula
        components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (productiveAutomataCapExpression components routes).Covers
          (family.word parameters) := by
  rw [family.eval_existsUncoveredParametersFormula_iff
      hnonempty components routes]
  simp only [CapExpression.Uncovered]
  push_neg
  rfl

noncomputable def allParametersCoveredFormula
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    NatPresburger 0 :=
  NatPresburger.universalClosure arity
    (family.productiveAutomataExpressionCoverageFormula
      components routes)

theorem eval_allParametersCoveredFormula_iff
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.allParametersCoveredFormula
      components routes).Eval Fin.elim0 ↔
      ∀ parameters : Fin arity → Nat,
        (productiveAutomataCapExpression components routes).Covers
          (family.word parameters) := by
  rw [allParametersCoveredFormula,
    NatPresburger.eval_universalClosure_iff]
  constructor
  · intro heval parameters
    exact
      (family.eval_productiveAutomataExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).1
        (heval parameters)
  · intro hcovered parameters
    exact
      (family.eval_productiveAutomataExpressionCoverageFormula_iff_covers
        hnonempty parameters components routes).2
        (hcovered parameters)

theorem eval_allParametersCoveredFormula_iff_not_existsUncovered
    [Fintype α] [Fintype Q₁] [Fintype Q₂] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (routes : List (DFA α QR)) :
    (family.allParametersCoveredFormula
        components routes).Eval Fin.elim0 ↔
      ¬ (family.existsUncoveredParametersFormula
          components routes).Eval Fin.elim0 := by
  rw [family.eval_allParametersCoveredFormula_iff
      hnonempty components routes,
    family.not_eval_existsUncoveredParametersFormula_iff_all_covered
      hnonempty components routes]

theorem eval_existsUncoveredParametersFormula_finPad_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components :
      List (ProductiveCapPair α (Fin n₁) (Fin n₂)))
    (routes : List (DFA α QR))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    (family.existsUncoveredParametersFormula
        (components.map fun component =>
          component.finPad hleft hright) routes).Eval Fin.elim0 ↔
      (family.existsUncoveredParametersFormula
        components routes).Eval Fin.elim0 := by
  rw [family.eval_existsUncoveredParametersFormula_iff
      hnonempty
      (components.map fun component =>
        component.finPad hleft hright) routes,
    family.eval_existsUncoveredParametersFormula_iff
      hnonempty components routes,
    productiveAutomataCapExpression_finPad]

theorem eval_allParametersCoveredFormula_finPad_iff
    [Fintype α] [Fintype QR]
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (components :
      List (ProductiveCapPair α (Fin n₁) (Fin n₂)))
    (routes : List (DFA α QR))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    (family.allParametersCoveredFormula
        (components.map fun component =>
          component.finPad hleft hright) routes).Eval Fin.elim0 ↔
      (family.allParametersCoveredFormula
        components routes).Eval Fin.elim0 := by
  rw [family.eval_allParametersCoveredFormula_iff
      hnonempty
      (components.map fun component =>
        component.finPad hleft hright) routes,
    family.eval_allParametersCoveredFormula_iff
      hnonempty components routes,
    productiveAutomataCapExpression_finPad]

end LinearWordFamily

end NSSE
