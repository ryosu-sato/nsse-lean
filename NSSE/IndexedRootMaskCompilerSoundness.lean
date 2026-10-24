import NSSE.IndexedRootMaskSemantics
import NSSE.LabelledGeneralizedStateRules

/-!
# Avoider soundness of the indexed-query mask compiler

The finite Horn evaluator is interpreted directly by existence of an
avoider.  At a terminal, one representative candidate word together with
the full indexed forbidden mask gives that avoider.  Nonterminal rule
soundness is left as the concrete response-realization obligation.
-/

namespace NSSE

universe u

theorem decideIndexedRootMaskState_sound
    (I : SOAInstance α)
    (base : NumberedRuleSystem Tag)
    (atomCount : Nat)
    (guardedRequired : Tag → List Nat)
    (labels : TransitionMaskLabels Tag)
    (terminalWitness :
      ∀ state :
          ValidGeneralizedState Tag atomCount
            I.indexedRootQueryEnumeration.values.length,
        base.terminal state.1.tag = true →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              I.indexedRootQueryEnumeration guardedRequired)
            atomCount I.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word α,
          I.candidate word ∧
          I.IndexedMaskForbids state.1.forbidden word)
    (ruleAvoider :
      ∀ (parent :
            ValidGeneralizedState Tag atomCount
              I.indexedRootQueryEnumeration.values.length)
        (children :
          List
            (ValidGeneralizedState Tag atomCount
              I.indexedRootQueryEnumeration.values.length)),
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount
            I.indexedRootQueryEnumeration.values.length
            (allCanonicalForbiddenRequirement
              I.indexedRootQueryEnumeration guardedRequired)
            labels).enabled parent children = true →
        (∀ child ∈ children,
          ∃ word : Word α, I.Avoider word) →
        ∃ word : Word α, I.Avoider word)
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount
            I.indexedRootQueryEnumeration.values.length
            (allCanonicalForbiddenRequirement
              I.indexedRootQueryEnumeration guardedRequired)
            labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        base atomCount
          I.indexedRootQueryEnumeration.values.length
          (allCanonicalForbiddenRequirement
            I.indexedRootQueryEnumeration guardedRequired)
          labels index = true) :
    ∃ word : Word α, I.Avoider word := by
  let system :=
    requiredLabelledGeneralizedStateRuleSystem
      base atomCount I.indexedRootQueryEnumeration.values.length
        (allCanonicalForbiddenRequirement
          I.indexedRootQueryEnumeration guardedRequired)
        labels
  have hsound :=
    decideRequiredLabelledState_sound
      base atomCount I.indexedRootQueryEnumeration.values.length
      (allCanonicalForbiddenRequirement
        I.indexedRootQueryEnumeration guardedRequired)
      labels
      (fun _ => ∃ word : Word α, I.Avoider word)
      (fun state hterminal => by
        have hparts :
            base.terminal state.1.tag = true ∧
            requiredMasksTerminal
              (allCanonicalForbiddenRequirement
                I.indexedRootQueryEnumeration guardedRequired)
              atomCount I.indexedRootQueryEnumeration.values.length
              state = true := by
          simpa [system, requiredLabelledGeneralizedStateRuleSystem,
            labelledGeneralizedStateRuleSystem,
            transitionGeneralizedStateRuleSystem] using hterminal
        obtain ⟨word, hcandidate, hforbids⟩ :=
          terminalWitness state hparts.1 hparts.2
        exact ⟨word,
          I.avoider_of_allCanonicalMaskTerminal
            guardedRequired atomCount state word hparts.2
            hcandidate hforbids⟩)
      ruleAvoider index hindex haccept
  obtain ⟨_, _, havoider⟩ := hsound
  exact havoider

theorem decideIndexedRootMaskState_sound_of_nonempty_rules
    (I : SOAInstance α)
    (base : NumberedRuleSystem Tag)
    (atomCount : Nat)
    (guardedRequired : Tag → List Nat)
    (labels : TransitionMaskLabels Tag)
    (terminalWitness :
      ∀ state :
          ValidGeneralizedState Tag atomCount
            I.indexedRootQueryEnumeration.values.length,
        base.terminal state.1.tag = true →
        requiredMasksTerminal
            (allCanonicalForbiddenRequirement
              I.indexedRootQueryEnumeration guardedRequired)
            atomCount I.indexedRootQueryEnumeration.values.length
            state = true →
        ∃ word : Word α,
          I.candidate word ∧
          I.IndexedMaskForbids state.1.forbidden word)
    (enabled_nonempty :
      ∀ parent children,
        base.enabled parent children = true →
        children ≠ [])
    (index : Nat)
    (hindex :
      index <
        (requiredLabelledGeneralizedStateRuleSystem
          base atomCount
            I.indexedRootQueryEnumeration.values.length
            (allCanonicalForbiddenRequirement
              I.indexedRootQueryEnumeration guardedRequired)
            labels).states.stateCount)
    (haccept :
      decideRequiredLabelledState
        base atomCount
          I.indexedRootQueryEnumeration.values.length
          (allCanonicalForbiddenRequirement
            I.indexedRootQueryEnumeration guardedRequired)
          labels index = true) :
    ∃ word : Word α, I.Avoider word := by
  apply decideIndexedRootMaskState_sound
    I base atomCount guardedRequired labels terminalWitness
  · intro parent children henabled hchildren
    have hbase : base.enabled parent.1.tag
        (children.map fun child => child.1.tag) = true := by
      simp only [requiredLabelledGeneralizedStateRuleSystem,
        labelledGeneralizedStateRuleSystem,
        transitionGeneralizedStateRuleSystem,
        Bool.and_eq_true] at henabled
      exact henabled.1
    have htags :
        (children.map fun child => child.1.tag) ≠ [] :=
      enabled_nonempty parent.1.tag
        (children.map fun child => child.1.tag) hbase
    cases children with
    | nil =>
        exact False.elim (htags rfl)
    | cons child rest =>
        exact hchildren child (by simp)
  · exact hindex
  · exact haccept

end NSSE
