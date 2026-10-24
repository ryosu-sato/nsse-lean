import NSSE.NumberedTaggedCompiler
import NSSE.GeneralizedStateMaskProgress

/-!
# Building finite derivations from a decreasing unary step

If every state is terminal or has an enabled unary successor with a strictly
smaller natural-number measure, well-founded induction constructs a finite
tagged derivation.
-/

namespace NSSE

theorem NumberedRuleSystem.taggedDerives_of_terminal_or_unary_descent
    (system : NumberedRuleSystem State)
    (measure : State → Nat)
    (progress :
      ∀ state,
        system.terminal state = true ∨
          ∃ child,
            1 ∈ system.arities ∧
            system.enabled state [child] = true ∧
            measure child < measure state)
    (state : State) :
    system.TaggedDerives state := by
  have main :
      ∀ n, ∀ current : State,
        measure current = n →
        system.TaggedDerives current := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro current hmeasure
        rcases progress current with hterminal | hstep
        · exact .terminal hterminal
        · obtain ⟨child, harity, henabled, hdecrease⟩ := hstep
          apply NumberedRuleSystem.TaggedDerives.rule
            (children := [child]) harity henabled
          intro found hfound
          simp only [List.mem_singleton] at hfound
          subst found
          apply ih (measure child)
          · simpa [hmeasure] using hdecrease
          · rfl
  exact main (measure state) state rfl

theorem NumberedRuleSystem.taggedDerives_of_invariant_unary_descent
    (system : NumberedRuleSystem State)
    (measure : State → Nat)
    (Good : State → Prop)
    (progress :
      ∀ state,
        Good state →
        system.terminal state = true ∨
          ∃ child,
            Good child ∧
            1 ∈ system.arities ∧
            system.enabled state [child] = true ∧
            measure child < measure state)
    (state : State)
    (hgood : Good state) :
    system.TaggedDerives state := by
  have main :
      ∀ n, ∀ current : State,
        measure current = n →
        Good current →
        system.TaggedDerives current := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro current hmeasure hcurrent
        rcases progress current hcurrent with hterminal | hstep
        · exact .terminal hterminal
        · obtain ⟨child, hchild, harity, henabled, hdecrease⟩ := hstep
          apply NumberedRuleSystem.TaggedDerives.rule
            (children := [child]) harity henabled
          intro found hfound
          simp only [List.mem_singleton] at hfound
          subst found
          apply ih (measure child)
          · simpa [hmeasure] using hdecrease
          · rfl
          · exact hchild
  exact main (measure state) state rfl hgood

theorem NumberedRuleSystem.taggedDerives_of_terminal_or_residual_or_unary_descent
    (system : NumberedRuleSystem State)
    (measure : State → Nat)
    (Residual : State → Prop)
    (residualDerives :
      ∀ state, Residual state → system.TaggedDerives state)
    (progress :
      ∀ state,
        system.terminal state = true ∨
          Residual state ∨
          ∃ child,
            1 ∈ system.arities ∧
            system.enabled state [child] = true ∧
            measure child < measure state)
    (state : State) :
    system.TaggedDerives state := by
  have main :
      ∀ n, ∀ current : State,
        measure current = n →
        system.TaggedDerives current := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro current hmeasure
        rcases progress current with
          hterminal | hresidual | hstep
        · exact .terminal hterminal
        · exact residualDerives current hresidual
        · obtain ⟨child, harity, henabled, hdecrease⟩ := hstep
          apply NumberedRuleSystem.TaggedDerives.rule
            (children := [child]) harity henabled
          intro found hfound
          simp only [List.mem_singleton] at hfound
          subst found
          apply ih (measure child)
          · simpa [hmeasure] using hdecrease
          · rfl
  exact main (measure state) state rfl

theorem NumberedRuleSystem.taggedDerives_of_invariant_terminal_or_residual_or_unary_descent
    (system : NumberedRuleSystem State)
    (measure : State → Nat)
    (Good Residual : State → Prop)
    (residualDerives :
      ∀ state, Good state → Residual state →
        system.TaggedDerives state)
    (progress :
      ∀ state,
        Good state →
        system.terminal state = true ∨
          Residual state ∨
          ∃ child,
            Good child ∧
            1 ∈ system.arities ∧
            system.enabled state [child] = true ∧
            measure child < measure state)
    (state : State)
    (hgood : Good state) :
    system.TaggedDerives state := by
  have main :
      ∀ n, ∀ current : State,
        measure current = n →
        Good current →
        system.TaggedDerives current := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro current hmeasure hcurrent
        rcases progress current hcurrent with
          hterminal | hresidual | hstep
        · exact .terminal hterminal
        · exact residualDerives current hcurrent hresidual
        · obtain ⟨child, hchild, harity, henabled, hdecrease⟩ :=
            hstep
          apply NumberedRuleSystem.TaggedDerives.rule
            (children := [child]) harity henabled
          intro found hfound
          simp only [List.mem_singleton] at hfound
          subst found
          apply ih (measure child)
          · simpa [hmeasure] using hdecrease
          · rfl
          · exact hchild
  exact main (measure state) state rfl hgood

theorem decideRequiredLabelled_of_terminal_or_capacity_descent
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (progress :
      ∀ state :
          ValidGeneralizedState Tag atomCount queryCount,
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels
          ).terminal state = true ∨
        ∃ child :
            ValidGeneralizedState Tag atomCount queryCount,
          1 ∈
            (requiredLabelledGeneralizedStateRuleSystem
              base atomCount queryCount requirement labels).arities ∧
          (requiredLabelledGeneralizedStateRuleSystem
            base atomCount queryCount requirement labels
            ).enabled state [child] = true ∧
          remainingMaskCapacity atomCount queryCount child.1 <
            remainingMaskCapacity atomCount queryCount state.1)
    (initial :
      ValidGeneralizedState Tag atomCount queryCount) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
        ).states.decode index = some initial ∧
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true := by
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
  have hderive : system.TaggedDerives initial := by
    apply system.taggedDerives_of_terminal_or_unary_descent
      (fun state =>
        remainingMaskCapacity atomCount queryCount state.1)
    exact progress
  obtain ⟨index, hindex, hdecode⟩ :=
    system.states.exists_index_decode initial
  refine ⟨index, hdecode, ?_⟩
  exact
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).2
      ⟨initial, hdecode, hderive⟩

theorem decideRequiredLabelled_of_invariant_capacity_descent
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (Good :
      ValidGeneralizedState Tag atomCount queryCount → Prop)
    (progress :
      ∀ state :
          ValidGeneralizedState Tag atomCount queryCount,
        Good state →
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels
          ).terminal state = true ∨
        ∃ child :
            ValidGeneralizedState Tag atomCount queryCount,
          Good child ∧
          1 ∈
            (requiredLabelledGeneralizedStateRuleSystem
              base atomCount queryCount requirement labels).arities ∧
          (requiredLabelledGeneralizedStateRuleSystem
            base atomCount queryCount requirement labels
            ).enabled state [child] = true ∧
          remainingMaskCapacity atomCount queryCount child.1 <
            remainingMaskCapacity atomCount queryCount state.1)
    (initial :
      ValidGeneralizedState Tag atomCount queryCount)
    (hgood : Good initial) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
        ).states.decode index = some initial ∧
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true := by
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
  have hderive : system.TaggedDerives initial := by
    apply system.taggedDerives_of_invariant_unary_descent
      (fun state =>
        remainingMaskCapacity atomCount queryCount state.1)
      Good progress initial hgood
  obtain ⟨index, hindex, hdecode⟩ :=
    system.states.exists_index_decode initial
  refine ⟨index, hdecode, ?_⟩
  exact
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).2
      ⟨initial, hdecode, hderive⟩

theorem decideRequiredLabelled_of_invariant_terminal_or_residual_or_capacity_descent
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (Good Residual :
      ValidGeneralizedState Tag atomCount queryCount → Prop)
    (residualDerives :
      ∀ state,
        Good state →
        Residual state →
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels
          ).TaggedDerives state)
    (progress :
      ∀ state :
          ValidGeneralizedState Tag atomCount queryCount,
        Good state →
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount queryCount requirement labels
          ).terminal state = true ∨
        Residual state ∨
        ∃ child :
            ValidGeneralizedState Tag atomCount queryCount,
          Good child ∧
          1 ∈
            (requiredLabelledGeneralizedStateRuleSystem
              base atomCount queryCount requirement labels).arities ∧
          (requiredLabelledGeneralizedStateRuleSystem
            base atomCount queryCount requirement labels
            ).enabled state [child] = true ∧
          remainingMaskCapacity atomCount queryCount child.1 <
            remainingMaskCapacity atomCount queryCount state.1)
    (initial :
      ValidGeneralizedState Tag atomCount queryCount)
    (hgood : Good initial) :
    ∃ index,
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
        ).states.decode index = some initial ∧
      decideRequiredLabelledState
        base atomCount queryCount requirement labels index = true := by
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
  have hderive : system.TaggedDerives initial := by
    apply
      system.taggedDerives_of_invariant_terminal_or_residual_or_unary_descent
        (fun state =>
          remainingMaskCapacity atomCount queryCount state.1)
        Good Residual residualDerives progress initial hgood
  obtain ⟨index, hindex, hdecode⟩ :=
    system.states.exists_index_decode initial
  refine ⟨index, hdecode, ?_⟩
  exact
    (decideRequiredLabelledState_correct
      base atomCount queryCount requirement labels index hindex).2
      ⟨initial, hdecode, hderive⟩

end NSSE
