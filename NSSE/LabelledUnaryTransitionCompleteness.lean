import NSSE.LabelledGeneralizedStateCompleteness

/-!
# Canonical lifting of unary base transitions

The child masks of a labelled transition are determined by the parent masks
and the transition labels.  Hence every enabled unary base rule lifts to an
enabled generalized rule with the canonical labelled child.
-/

namespace NSSE

def labelledValidChild
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount queryCount)
    (childTag : Tag) :
    ValidGeneralizedState Tag atomCount queryCount :=
  ⟨labelledChildState labels parent.1.tag
      parent.1.guarded parent.1.forbidden childTag,
    labelledChildState_valid labels parent.1.tag childTag
      parent.1.guarded parent.1.forbidden parent.2⟩

theorem requiredLabelled_enabled_labelledValidChild
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount queryCount)
    (childTag : Tag)
    (hbase : base.enabled parent.1.tag [childTag] = true) :
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
      ).enabled parent [labelledValidChild labels parent childTag] =
        true := by
  rw [requiredLabelled_enabled_iff]
  constructor
  · simpa [labelledValidChild, labelledChildState] using hbase
  · simp [allStateMasksFollow, labelledValidChild,
      labelledChildState, maskEqB_correct]

theorem requiredLabelled_derives_of_unary_base
    (base : NumberedRuleSystem Tag)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement Tag)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount queryCount)
    (childTag : Tag)
    (harity : 1 ∈ base.arities)
    (hbase : base.enabled parent.1.tag [childTag] = true)
    (hchild :
      (requiredLabelledGeneralizedStateRuleSystem
        base atomCount queryCount requirement labels
        ).TaggedDerives
          (labelledValidChild labels parent childTag)) :
    (requiredLabelledGeneralizedStateRuleSystem
      base atomCount queryCount requirement labels
      ).TaggedDerives parent := by
  apply NumberedRuleSystem.TaggedDerives.rule
    (children := [labelledValidChild labels parent childTag])
  · simpa [requiredLabelledGeneralizedStateRuleSystem,
      labelledGeneralizedStateRuleSystem,
      transitionGeneralizedStateRuleSystem] using harity
  · exact requiredLabelled_enabled_labelledValidChild
      base atomCount queryCount requirement labels
      parent childTag hbase
  · intro child hmember
    simp only [List.mem_singleton] at hmember
    subst child
    exact hchild

end NSSE
