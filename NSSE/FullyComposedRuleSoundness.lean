import NSSE.FiniteLoopRuleSoundness
import NSSE.AttachmentResponseRuleSoundness
import NSSE.UnifiedAtomicRuleSoundness

/-!
# Semantic soundness of the fully composed attachment compiler

The full dispatcher is the merge of the finite loop family, the unary
attachment-response family, and the unified atomic family.  This theorem
lists exactly the five local semantic obligations and combines the three
family proofs in the same nesting order as `fullyComposedRuleTests`.
-/

namespace NSSE

universe u

theorem fullyComposedRuleTests_semanticallySound
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (nonidentity_sound :
      ∀ tag loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        meaning tag)
    (side_sound :
      ∀ control cut parent child,
        intervalSideEnabled attachment
          control cut parent child = true →
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
      (fullyComposedRuleTests summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal)
      meaning := by
  let loopSound :=
    finiteLoopRuleTests_semanticallySound
      summaryOf meaning nonidentity_sound
  let responseSound :=
    attachmentResponseRuleTests_semanticallySound
      (intervalSideEnabled attachment) localEnabled meaning
      side_sound local_response_sound
  let atomicSound :=
    unifiedAtomicRuleTests_semanticallySound
      (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
      (LCA := NatInterval) (Macro := Macro)
      (Wire := FiniteLoopLabel Wire LoopId)
      (QClass := QClass)
      I left right rightFinal event w j t localTerminal
      meaning guard_sound local_terminal_sound
  exact loopSound.merge (responseSound.merge atomicSound)

def fullyComposedInitialSideRootRealizationSemantics
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance β)
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (roots : List (InitialSideRoot Ctl Cut))
    (meaning :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass → Prop)
    (nonidentity_sound :
      ∀ tag loopId,
        tag.loopId? = some loopId →
        ¬ IdentityLoop (summaryOf loopId) →
        meaning tag)
    (side_sound :
      ∀ control cutValue parent child,
        intervalSideEnabled attachment
          control cutValue parent child = true →
        meaning child →
        meaning (.side control cutValue parent))
    (local_response_sound :
      ∀ control cutValue parent child,
        localEnabled control cutValue parent child = true →
        meaning child →
        meaning (.side control cutValue parent))
    (guard_sound :
      ∀ control cutValue query,
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true →
        meaning (.bounded control cutValue (.inl query)))
    (local_terminal_sound :
      ∀ control cutValue localId,
        localTerminal localId = true →
        meaning (.bounded control cutValue (.inr localId)))
    (selected_side_sound :
      ∀ root ∈ roots,
        meaning (.side root.control root.cut root.parent) →
        ∃ word : Word β, soa.Avoider word) :
    InitialSideRootRealizationSemantics soa
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient)
      roots := by
  let sound :=
    fullyComposedRuleTests_semanticallySound
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal meaning
      nonidentity_sound side_sound local_response_sound
      guard_sound local_terminal_sound
  exact sound.toInitialSideRootRealizationSemantics
    ctl cut ori intervals macros
    (FiniteLoopLabel.enumeration wires loops)
    (unifiedAtomicEnumeration
      (finiteGuardQueryEnumeration I left right event w j t) locals)
    quotient roots selected_side_sound

end NSSE
