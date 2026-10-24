import NSSE.RegisteredStructuralDispatcher
import NSSE.UnifiedFiniteDispatcher

/-!
# Registered structural emitters in the unified dispatcher

The isolated finite-loop dispatcher already recognized every registered
structural emitter.  This module proves that adding interval-side and
bounded-response rules does not change that semantics.
-/

namespace NSSE

universe u

namespace RegisteredStructuralStep

theorem emittedTag_unifiedDerives_iff_nonidentity
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    (summaryOf : LoopId → LoopSummary Wire)
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut NatInterval Macro)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    (unifiedFiniteRuleSystem summaryOf attachment I left right
      rightFinal event w j t ctl cut orientation intervals macros wires
      loops quotient).TaggedDerives
        (registered.emittedTag
          (Atom :=
            FirstEventFiniteGuardQuery I left right event w j t)
          context) ↔
      ¬ IdentityLoop (summaryOf registered.loopId) := by
  rw [unifiedFinite_structural_taggedDerives_iff
    summaryOf attachment I left right rightFinal event w j t
    ctl cut orientation intervals macros wires loops quotient
    (registered.emittedTag
      (Atom := FirstEventFiniteGuardQuery I left right event w j t)
      context)
    (by simp)]
  constructor
  · rintro ⟨loopId, hloop, hnonidentity⟩
    rw [registered.emittedTag_loopId] at hloop
    cases Option.some.inj hloop
    exact hnonidentity
  · intro hnonidentity
    exact ⟨registered.loopId,
      registered.emittedTag_loopId context, hnonidentity⟩

theorem emittedTag_unifiedDerives_iff_terminalHorn
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    (summaryOf : LoopId → LoopSummary Wire)
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut NatInterval Macro)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    (unifiedFiniteRuleSystem summaryOf attachment I left right
      rightFinal event w j t ctl cut orientation intervals macros wires
      loops quotient).TaggedDerives
        (registered.emittedTag
          (Atom :=
            FirstEventFiniteGuardQuery I left right event w j t)
          context) ↔
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            registered.source registered.step).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            registered.source registered.step).summary).root := by
  rw [registered.emittedTag_unifiedDerives_iff_nonidentity
    summaryOf context attachment I left right rightFinal event w j t
    ctl cut orientation intervals macros wires loops quotient,
    registered.summary_registered,
    loopCompilerTerminalHornFamily_derives_iff,
    LoopUpdate.IsIdentity]

end RegisteredStructuralStep

end NSSE
