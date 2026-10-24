import NSSE.LocalAttachmentResponse
import NSSE.UnifiedAtomicDispatcher

/-!
# Registering local mismatch terminals in the unified atom alphabet

A fixed compiler assigns each relevant ordered local attachment a
finite `LocalId`.  Registration equates its lookup bit with the already
verified mismatch-Horn decision.
-/

namespace NSSE

universe u

def OrderedInsertionAttachment.mismatchTerminal
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) : Bool :=
  decideHornState
    (insertionSquareMismatchHornFamily
      attachment.left attachment.middle attachment.right
      attachment.payload).compiler
    (insertionSquareMismatchHornFamily
      attachment.left attachment.middle attachment.right
      attachment.payload).root

structure RegisteredLocalMismatch
    (α LocalId : Type u) [DecidableEq α]
    (localTerminal : LocalId → Bool) where
  attachment : OrderedInsertionAttachment α
  localId : LocalId
  terminal_registered :
    localTerminal localId = attachment.mismatchTerminal

namespace RegisteredLocalMismatch

theorem atomTag_derives_iff_mismatch
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (registered : RegisteredLocalMismatch α LocalId localTerminal)
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) :
    (fullyUnifiedRuleSystem summaryOf domains I left right rightFinal
      event w j t localTerminal ctl cut ori intervals macros wires loops
      locals quotient).TaggedDerives
        (.bounded control cutValue (.inr registered.localId)) ↔
      Word.insertAt registered.attachment.base
          registered.attachment.payload registered.attachment.leftSlot ≠
        Word.insertAt registered.attachment.base
          registered.attachment.payload
          registered.attachment.rightSlot := by
  rw [fullyUnified_localAtom_taggedDerives_iff,
    registered.terminal_registered]
  change
    decideHornState
        (insertionSquareMismatchHornFamily
          registered.attachment.left registered.attachment.middle
          registered.attachment.right
          registered.attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          registered.attachment.left registered.attachment.middle
          registered.attachment.right
          registered.attachment.payload).root = true ↔ _
  exact registered.attachment.decideMismatchRoot_correct

end RegisteredLocalMismatch

end NSSE
