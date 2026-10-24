import NSSE.TaggedRuleDispatcher

/-!
# Inert identity loops for tagged compilers

An identity loop has one child, exactly equal to its parent.  Under the
least inductive derivability semantics it cannot create a derivation.
This module proves that adding every such loop to an arbitrary dispatched
rule family preserves tagged derivability exactly.
-/

namespace NSSE

universe u

abbrev DispatchTag
    (Ctl Cut Ori LCA Macro Wire Atom QClass : Type u) :=
  CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass

def identityTaggedRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass] :
    CompilerTagRuleTests
      Ctl Cut Ori LCA Macro Wire Atom QClass where
  arities := fun _ => [1]
  terminal := fun _ _ => false
  enabled := fun _ parent children =>
    decide (children = [parent])

theorem identity_dispatchTerminal_false
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tag : DispatchTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    (identityTaggedRuleTests.dispatchTerminal tag) = false := by
  rfl

theorem identity_dispatchEnabled_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (parent : DispatchTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (children :
      List (DispatchTag Ctl Cut Ori LCA Macro Wire Atom QClass)) :
    identityTaggedRuleTests.dispatchEnabled parent children = true ↔
      children = [parent] := by
  simp only [CompilerTagRuleTests.dispatchEnabled,
    identityTaggedRuleTests, List.mem_singleton,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hchildren
    subst children
    simp

theorem identity_taggedDerives_false
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : DispatchTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    ¬ (identityTaggedRuleTests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag := by
  intro hderive
  induction hderive with
  | terminal hterminal =>
      simp [CompilerTagRuleTests.ruleSystem,
        identityTaggedRuleTests,
        CompilerTagRuleTests.dispatchTerminal] at hterminal
  | @rule parent children harity henabled childDerives ih =>
      have hchildren : children = [parent] :=
        (identity_dispatchEnabled_iff parent children).1 henabled
      subst children
      exact ih parent (by simp)

theorem merge_identity_taggedDerives_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : DispatchTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    ((identityTaggedRuleTests.merge tests).ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      (tests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag := by
  constructor
  · intro hderive
    induction hderive with
    | @terminal state hterminal =>
        have hterminal' :
            tests.dispatchTerminal state = true := by
          have h :=
            ((CompilerTagRuleTests.merge_dispatchTerminal_true_iff
              identityTaggedRuleTests tests state).1 hterminal)
          rcases h with hidentity | htests
          · simp [identity_dispatchTerminal_false] at hidentity
          · exact htests
        exact NumberedRuleSystem.TaggedDerives.terminal hterminal'
    | @rule parent children harity henabled childDerives ih =>
        have hcases :=
          (CompilerTagRuleTests.merge_dispatchEnabled_true_iff
            identityTaggedRuleTests tests parent children).1 henabled
        rcases hcases with hidentity | htests
        · have hchildren :=
            (identity_dispatchEnabled_iff parent children).1 hidentity
          subst children
          exact ih parent (by simp)
        · apply NumberedRuleSystem.TaggedDerives.rule
          · exact tests.kind_arity_mem_allArities parent.kind
              ((tests.dispatchEnabled_correct
                parent children).1 htests).1
          · exact htests
          · exact ih
  · intro hderive
    induction hderive with
    | @terminal state hterminal =>
        apply NumberedRuleSystem.TaggedDerives.terminal
        exact
          (CompilerTagRuleTests.merge_dispatchTerminal_true_iff
            identityTaggedRuleTests tests state).2 (Or.inr hterminal)
    | @rule parent children harity henabled childDerives ih =>
        have hbaseDispatch :
            tests.dispatchEnabled parent children = true := henabled
        have hmergedDispatch :
            (identityTaggedRuleTests.merge tests
              ).dispatchEnabled parent children = true :=
          (CompilerTagRuleTests.merge_dispatchEnabled_true_iff
            identityTaggedRuleTests tests parent children).2
            (Or.inr hbaseDispatch)
        apply NumberedRuleSystem.TaggedDerives.rule
        · exact
            (identityTaggedRuleTests.merge tests
              ).kind_arity_mem_allArities parent.kind
              (((identityTaggedRuleTests.merge tests
                ).dispatchEnabled_correct parent children).1
                hmergedDispatch).1
        · exact hmergedDispatch
        · exact ih

theorem merge_identity_decideState_iff
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (index : Nat)
    (hindex :
      index <
        (tests.ruleSystem
          ctl cut ori lca macros wire atom quotient).states.stateCount) :
    decideHornState
        ((identityTaggedRuleTests.merge tests).ruleSystem
          ctl cut ori lca macros wire atom quotient).compiler
        index = true ↔
      decideHornState
        (tests.ruleSystem
          ctl cut ori lca macros wire atom quotient).compiler
        index = true := by
  let merged :=
    (identityTaggedRuleTests.merge tests).ruleSystem
      ctl cut ori lca macros wire atom quotient
  let original :=
    tests.ruleSystem ctl cut ori lca macros wire atom quotient
  have hmergedIndex : index < merged.states.stateCount := hindex
  rw [merged.decideState_correct index hmergedIndex,
    original.decideState_correct index hindex]
  constructor
  · rintro ⟨state, hdecode, hderive⟩
    exact ⟨state, hdecode,
      (merge_identity_taggedDerives_iff
        tests ctl cut ori lca macros wire atom quotient state).1
        hderive⟩
  · rintro ⟨state, hdecode, hderive⟩
    exact ⟨state, hdecode,
      (merge_identity_taggedDerives_iff
        tests ctl cut ori lca macros wire atom quotient state).2
        hderive⟩

end NSSE
