import NSSE.RankedAttachmentResponseDispatcher
import NSSE.FiniteLoopRuleSoundness
import NSSE.AttachmentResponseRuleSoundness
import NSSE.UnifiedAtomicRuleSoundness

/-!
# Semantic soundness obligations for the ranked compiler

This theorem identifies the exact realization obligations for a fixed
finite rank compiler.  In particular, an exhaustive response table is
usable for decision only when every enabled registered edge preserves
the chosen semantic meaning.
-/

namespace NSSE

theorem rankedFullyComposedRuleTests_semanticallySound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass → Prop)
    (nonidentity_sound :
      ∀ tag loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        meaning tag)
    (side_sound :
      ∀ control cut parent child,
        rankedSideEnabled control cut parent child = true →
        meaning child →
        meaning (.side control cut parent))
    (local_response_sound :
      ∀ control cut parent child,
        localEnabled control cut parent child = true →
        meaning child →
        meaning (.side control cut parent))
    (guard_sound :
      ∀ control cut query,
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true →
        meaning (.bounded control cut (.inl query)))
    (local_terminal_sound :
      ∀ control cut localId,
        localTerminal localId = true →
        meaning (.bounded control cut (.inr localId))) :
    CompilerTagRuleTests.SemanticallySound
      (rankedFullyComposedRuleTests summaryOf
        I left right rightFinal event w j t height
        localEnabled localTerminal)
      meaning := by
  let loopSound :=
    finiteLoopRuleTests_semanticallySound
      summaryOf meaning nonidentity_sound
  let responseSound :=
    attachmentResponseRuleTests_semanticallySound
      rankedSideEnabled localEnabled meaning
      side_sound local_response_sound
  let atomicSound :=
    unifiedAtomicRuleTests_semanticallySound
      (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
      (LCA := SideRank height) (Macro := Macro)
      (Wire := FiniteLoopLabel Wire LoopId)
      (QClass := QClass)
      I left right rightFinal event w j t localTerminal
      meaning guard_sound local_terminal_sound
  exact loopSound.merge (responseSound.merge atomicSound)

theorem rankedFullyComposed_derives_meaning
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass → Prop)
    (sound :
      CompilerTagRuleTests.SemanticallySound
        (rankedFullyComposedRuleTests summaryOf
          I left right rightFinal event w j t height
          localEnabled localTerminal)
        meaning)
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass}
    (derive :
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height
        localEnabled localTerminal ctl cut ori macros wires loops
        locals quotient).TaggedDerives state) :
    meaning state := by
  exact sound.derives ctl cut ori (sideRankEnumeration height)
    macros (FiniteLoopLabel.enumeration wires loops)
    (unifiedAtomicEnumeration
      (finiteGuardQueryEnumeration I left right event w j t) locals)
    quotient derive

end NSSE
