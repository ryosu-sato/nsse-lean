import NSSE.TaggedRuleSoundness
import NSSE.UnifiedAtomicDispatcher

/-!
# Semantic soundness of unified atomic terminals

The unified atomic family has no rules.  Its only terminals are bounded
guard atoms and registered local atoms, so its semantic proof is exactly
the pair of corresponding terminal interpretations.
-/

namespace NSSE

universe u

theorem unifiedAtomicRuleTests_semanticallySound
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localTerminal : LocalId → Bool)
    (meaning :
      CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (guard_sound :
      ∀ control cut query,
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true →
        meaning (.bounded control cut (.inl query)))
    (local_sound :
      ∀ control cut localId,
        localTerminal localId = true →
        meaning (.bounded control cut (.inr localId))) :
    CompilerTagRuleTests.SemanticallySound
      (unifiedAtomicRuleTests
        (Ctl := Ctl) (Cut := Cut) (Ori := Ori) (LCA := LCA)
        (Macro := Macro) (Wire := Wire) (QClass := QClass)
        I left right rightFinal event w j t localTerminal)
      meaning where
  terminal := by
    intro state hterminal
    cases state with
    | nonstrong control cut lca macroData wire =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTag.kind] at hterminal
    | strong control cut macroData wire quotient =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTag.kind] at hterminal
    | hub control cut macroData wire =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTag.kind] at hterminal
    | copy control cut orientation macroData wire =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTag.kind] at hterminal
    | side control cut lca =>
        simp [unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTag.kind] at hterminal
    | bounded control cut atom =>
        cases atom with
        | inl query =>
            exact guard_sound control cut query (by
              simpa [unifiedAtomicRuleTests,
                CompilerTagRuleTests.dispatchTerminal,
                CompilerTag.kind] using hterminal)
        | inr localId =>
            exact local_sound control cut localId (by
              simpa [unifiedAtomicRuleTests,
                CompilerTagRuleTests.dispatchTerminal,
                CompilerTag.kind] using hterminal)
  enabled := by
    intro parent children henabled hchildren
    simp [unifiedAtomicRuleTests,
      CompilerTagRuleTests.dispatchEnabled] at henabled

end NSSE
