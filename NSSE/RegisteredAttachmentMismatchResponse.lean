import NSSE.RegisteredLocalMismatchAtom
import NSSE.RegisteredAttachmentResponseTable

/-!
# Registering a local mismatch as an attachment response

A registered local mismatch ID becomes one bounded atomic child.  When
the two insertions really differ, that child is terminal; placing its
edge in the finite response table therefore derives the enclosing side
root.
-/

namespace NSSE

universe u

theorem RegisteredLocalMismatch.singletonTable_side_derives_of_mismatch
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
    (control : Ctl) (cutValue : Cut) (parent : NatInterval)
    (hmismatch :
      Word.insertAt registered.attachment.base
          registered.attachment.payload registered.attachment.leftSlot ≠
        Word.insertAt registered.attachment.base
          registered.attachment.payload
          registered.attachment.rightSlot) :
    let child :
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass :=
      .bounded control cutValue (.inr registered.localId)
    let edge :
        FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId QClass :=
      {
        control := control
        cut := cutValue
        parent := parent
        child := child
      }
    (fullyComposedRuleSystem summaryOf domains
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled [edge]) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives (.side control cutValue parent) := by
  dsimp only
  let responseEdge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass :=
    {
      control := control
      cut := cutValue
      parent := parent
      child := .bounded control cutValue (.inr registered.localId)
    }
  change
    (fullyComposedRuleSystem summaryOf domains
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled [responseEdge]) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives
        (.side responseEdge.control responseEdge.cut responseEdge.parent)
  apply fullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (attachment := domains)
    (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := w)
    (j := j) (t := t)
    (edges := [responseEdge]) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (intervals := intervals)
    (macros := macros) (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient) (edge := responseEdge)
  · simp
  · apply fullyComposed_localAtom_derives
      (summaryOf := summaryOf) (attachment := domains)
      (I := I) (left := left) (right := right)
      (rightFinal := rightFinal) (event := event) (w := w)
      (j := j) (t := t)
      (edges := [responseEdge]) (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := ori) (intervals := intervals)
      (macros := macros) (wires := wires) (loops := loops)
      (locals := locals) (quotient := quotient)
      (control := control) (cutValue := cutValue)
      (localId := registered.localId)
    rw [registered.terminal_registered]
    exact registered.attachment.decideMismatchRoot_correct.mpr hmismatch

end NSSE
