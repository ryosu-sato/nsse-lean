import NSSE.TaggedRuleSoundness
import NSSE.FiniteLoopDispatcher

/-!
# Semantic soundness of finite structural-loop rules

A nonidentity loop is a terminal and needs one semantic interpretation.
An identity loop has the singleton child list `[parent]`, so preservation
is automatic from the child meaning and requires no additional semantic
assumption.
-/

namespace NSSE

universe u

theorem finiteLoopRuleTests_semanticallySound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq LoopId] [DecidableEq Atom] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (meaning :
      FiniteLoopCompilerTag
        Ctl Cut Ori LCA Macro Wire LoopId Atom QClass → Prop)
    (nonidentity_sound :
      ∀ tag loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        meaning tag) :
    CompilerTagRuleTests.SemanticallySound
      (finiteLoopRuleTests summaryOf) meaning where
  terminal := by
    intro state hterminal
    obtain ⟨loopId, hloop, hnonidentity⟩ :=
      (finiteLoop_dispatchTerminal_iff
        summaryOf state).1 hterminal
    exact nonidentity_sound
      state loopId hloop hnonidentity
  enabled := by
    intro parent children henabled hchildren
    obtain ⟨loopId, hloop, hidentity, hchildrenEq⟩ :=
      (finiteLoop_dispatchEnabled_iff
        summaryOf parent children).1 henabled
    subst children
    exact hchildren parent (by simp)

end NSSE
