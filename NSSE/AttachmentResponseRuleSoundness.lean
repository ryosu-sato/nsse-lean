import NSSE.TaggedRuleSoundness
import NSSE.AttachmentResponseDispatcher

/-!
# Semantic soundness of side and local attachment responses

The attachment response family has no terminals and only unary side
rules.  Its semantic proof therefore reduces exactly to two local
preservation statements: interval-side delegation preserves meaning, and
a registered local response edge preserves meaning.
-/

namespace NSSE

universe u

theorem attachmentResponseRuleTests_semanticallySound
    (sideEnabled localEnabled :
      Ctl → Cut → LCA →
        CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
          Bool)
    (meaning :
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass →
        Prop)
    (side_sound :
      ∀ control cut parent child,
        sideEnabled control cut parent child = true →
        meaning child →
        meaning (.side control cut parent))
    (local_sound :
      ∀ control cut parent child,
        localEnabled control cut parent child = true →
        meaning child →
        meaning (.side control cut parent)) :
    CompilerTagRuleTests.SemanticallySound
      (attachmentResponseRuleTests sideEnabled localEnabled)
      meaning where
  terminal := by
    intro state hterminal
    simp [attachmentResponseRuleTests,
      CompilerTagRuleTests.dispatchTerminal] at hterminal
  enabled := by
    intro parent children henabled hchildren
    cases parent with
    | nonstrong control cut interval macroData wire =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at henabled
    | strong control cut macroData wire quotient =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at henabled
    | hub control cut macroData wire =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at henabled
    | copy control cut orientation macroData wire =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at henabled
    | bounded control cut atom =>
        simp [attachmentResponseRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.kind] at henabled
    | side control cut parent =>
        obtain ⟨child, hchildrenEq, hresponse⟩ :=
          (attachmentResponse_dispatchEnabled_iff
            sideEnabled localEnabled control cut parent children
            ).1 henabled
        subst children
        have hchild : meaning child :=
          hchildren child (by simp)
        rcases hresponse with hside | hlocal
        · exact side_sound control cut parent child hside hchild
        · exact local_sound control cut parent child hlocal hchild

end NSSE
