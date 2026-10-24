import NSSE.MinimalAvoiderFactorForest
import NSSE.RegisteredAttachmentResponseTable

/-!
# The empty-word avoider as a registered bounded atom

No row can cover the empty word.  Hence an executable final-state test
for the candidate DFA decides exactly whether the empty word is an
avoider.  A fixed local ID registers that bit in the unified bounded
atomic alphabet.
-/

namespace NSSE

universe u

structure RegisteredEmptyAvoider
    (I : AutomataSOAInstance α QC QL QR)
    (candidateFinal : DFAFinalTest I.candidate)
    (LocalId : Type u)
    (localTerminal : LocalId → Bool) where
  localId : LocalId
  terminal_registered :
    localTerminal localId =
      candidateFinal.test I.candidate.start

namespace RegisteredEmptyAvoider

theorem atomTag_derives_iff_empty_avoider
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {candidateFinal : DFAFinalTest I.candidate}
    {localTerminal : LocalId → Bool}
    (registered :
      RegisteredEmptyAvoider I candidateFinal LocalId localTerminal)
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) :
    let system := fullyComposedRuleSystem
      (summaryOf := summaryOf) (attachment := domains)
      (I := I) (left := left) (right := right)
      (rightFinal := rightFinal) (event := event) (w := w)
      (j := j) (t := t)
      (localEnabled := attachmentResponseTableEnabled edges)
      (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := ori) (intervals := intervals)
      (macros := macros) (wires := wires) (loops := loops)
      (locals := locals) (quotient := quotient)
    system.TaggedDerives
        (.bounded control cutValue (.inr registered.localId)) ↔
      I.toSOA.Avoider [] := by
  dsimp only
  rw [fullyComposed_localAtom_taggedDerives_iff,
    registered.terminal_registered, candidateFinal.correct]
  change I.candidate.Accepts [] ↔ I.toSOA.Avoider []
  exact I.toSOA.avoider_nil_iff.symm

end RegisteredEmptyAvoider

end NSSE
