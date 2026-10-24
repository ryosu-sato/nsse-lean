import NSSE.DeferredTerminalRules
import NSSE.LabelledUnaryTransitionCompleteness

/-!
# Lifting deferred terminal provenance into labelled unary rules
-/

namespace NSSE

theorem deferredRequiredLabelled_unary_enabled
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement tests.Tag)
    (labels : TransitionMaskLabels tests.Tag)
    (parent :
      ValidGeneralizedState tests.Tag atomCount queryCount)
    (childTag : tests.Tag)
    (hterminal :
      tests.dispatchTerminal parent.1.tag = true)
    (hdefer : defer parent.1.tag = true)
    (hprovenance :
      provenance parent.1.tag childTag = true) :
    (requiredLabelledGeneralizedStateRuleSystem
      ((tests.deferTerminalsBy defer provenance).ruleSystem
        ctl cut ori lca macros wires atoms quotient)
      atomCount queryCount requirement labels
      ).enabled parent [labelledValidChild labels parent childTag] =
        true := by
  apply requiredLabelled_enabled_labelledValidChild
  change
    (tests.deferTerminalsBy defer provenance
      ).dispatchEnabled parent.1.tag [childTag] = true
  exact CompilerTagRuleTests.deferTerminalsBy_dispatchEnabled_deferred
    tests defer provenance parent.1.tag childTag
    hterminal hdefer hprovenance

theorem deferredRequiredLabelled_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (tests :
      CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire Atom QClass)
    (defer : tests.Tag → Bool)
    (provenance : tests.Tag → tests.Tag → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (atoms : Enumeration Atom) (quotient : Enumeration QClass)
    (atomCount queryCount : Nat)
    (requirement : TerminalMaskRequirement tests.Tag)
    (labels : TransitionMaskLabels tests.Tag)
    (parent :
      ValidGeneralizedState tests.Tag atomCount queryCount)
    (childTag : tests.Tag)
    (hterminal :
      tests.dispatchTerminal parent.1.tag = true)
    (hdefer : defer parent.1.tag = true)
    (hprovenance :
      provenance parent.1.tag childTag = true)
    (hchild :
      (requiredLabelledGeneralizedStateRuleSystem
        ((tests.deferTerminalsBy defer provenance).ruleSystem
          ctl cut ori lca macros wires atoms quotient)
        atomCount queryCount requirement labels
        ).TaggedDerives
          (labelledValidChild labels parent childTag)) :
    (requiredLabelledGeneralizedStateRuleSystem
      ((tests.deferTerminalsBy defer provenance).ruleSystem
        ctl cut ori lca macros wires atoms quotient)
      atomCount queryCount requirement labels
      ).TaggedDerives parent := by
  apply requiredLabelled_derives_of_unary_base
  · change 1 ∈ (tests.deferTerminalsBy defer provenance).allArities
    exact CompilerTagRuleTests.kind_arity_mem_allArities
      (tests.deferTerminalsBy defer provenance)
      parent.1.tag.kind
      (by simp [CompilerTagRuleTests.deferTerminalsBy])
  · change
      (tests.deferTerminalsBy defer provenance
        ).dispatchEnabled parent.1.tag [childTag] = true
    exact CompilerTagRuleTests.deferTerminalsBy_dispatchEnabled_deferred
      tests defer provenance parent.1.tag childTag
      hterminal hdefer hprovenance
  · exact hchild

end NSSE
