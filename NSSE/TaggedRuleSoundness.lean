import NSSE.SideRootRealizationSemantics
import NSSE.TaggedRuleDispatcher

/-!
# Compositional semantic soundness for tagged rule families

`CompilerTagRuleTests.merge` combines independently defined terminal and
rule families.  Semantic soundness should be proved in the same modular
way.  The structure below packages the two local preservation obligations,
and `SemanticallySound.merge` combines their proofs using the executable
dispatcher equivalences.
-/

namespace NSSE

universe u

namespace CompilerTagRuleTests

structure SemanticallySound
    (tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass)
    (meaning : tests.Tag → Prop) : Prop where
  terminal :
    ∀ state,
      tests.dispatchTerminal state = true →
      meaning state
  enabled :
    ∀ parent children,
      tests.dispatchEnabled parent children = true →
      (∀ child ∈ children, meaning child) →
      meaning parent

namespace SemanticallySound

theorem merge
    {left right :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass}
    {meaning : left.Tag → Prop}
    (leftSound : SemanticallySound left meaning)
    (rightSound : SemanticallySound right meaning) :
    SemanticallySound (left.merge right) meaning where
  terminal := by
    intro state hterminal
    rcases
        (merge_dispatchTerminal_true_iff
          left right state).1 hterminal with
      hleft | hright
    · exact leftSound.terminal state hleft
    · exact rightSound.terminal state hright
  enabled := by
    intro parent children henabled hchildren
    rcases
        (merge_dispatchEnabled_true_iff
          left right parent children).1 henabled with
      hleft | hright
    · exact leftSound.enabled
        parent children hleft hchildren
    · exact rightSound.enabled
        parent children hright hchildren

theorem derives
    {tests :
      CompilerTagRuleTests
        Ctl Cut Ori LCA Macro Wire Atom QClass}
    {meaning : tests.Tag → Prop}
    (sound : SemanticallySound tests meaning)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    {state : tests.Tag}
    (derive :
      (tests.ruleSystem
        ctl cut ori lca macros wire atom quotient
        ).TaggedDerives state) :
    meaning state :=
  derive.sound meaning sound.terminal sound.enabled

def toInitialSideRootRealizationSemantics
    {I : SOAInstance α}
    {tests :
      CompilerTagRuleTests
        Ctl Cut Ori NatInterval Macro Wire Atom QClass}
    {meaning : tests.Tag → Prop}
    (sound : SemanticallySound tests meaning)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (roots : List (InitialSideRoot Ctl Cut))
    (selectedSideSound :
      ∀ root ∈ roots,
        meaning (.side root.control root.cut root.parent) →
        ∃ word : Word α, I.Avoider word) :
    InitialSideRootRealizationSemantics I
      (tests.ruleSystem
        ctl cut ori intervals macros wire atom quotient)
      roots where
  meaning := meaning
  terminal_sound := sound.terminal
  rule_sound := sound.enabled
  selected_side_sound := selectedSideSound

end SemanticallySound

end CompilerTagRuleTests

end NSSE
