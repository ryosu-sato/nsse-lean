import NSSE.LongForestSideRootExtraction
import NSSE.RegisteredAttachmentResponseTable
import NSSE.RegisteredLocalMismatchAtom

/-!
# Finite-table handler for extracted mismatch attachments

A fixed global compiler assigns each relevant extracted attachment a
selected side root and a local mismatch ID.  One registration entry
records the exact terminal bit and membership of its response edge in
the finite table.  The main theorem turns a semantic insertion mismatch
into derivation of that selected side root in the fixed fully composed
system.
-/

namespace NSSE

universe u

structure FiniteMismatchResponseEntry
    [DecidableEq α]
    (attachment : ForestWordAttachment α)
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (localTerminal : LocalId → Bool) where
  root : InitialSideRoot Ctl Cut
  root_mem : root ∈ sideRoots
  parent_eq : root.parent = attachment.parent
  localId : LocalId
  terminal_registered :
    localTerminal localId =
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).mismatchTerminal
  edge_mem :
    ({
      control := root.control
      cut := root.cut
      parent := root.parent
      child := .bounded root.control root.cut (.inr localId)
    } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
      Guard LocalId QClass) ∈ edges

namespace FiniteMismatchResponseEntry

theorem side_derives_of_mismatch
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    {attachment : ForestWordAttachment α}
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (entry :
      FiniteMismatchResponseEntry attachment sideRoots
        edges localTerminal)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (hmismatch :
      let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      Word.insertAt ordered.base attachment.payload ordered.leftSlot ≠
        Word.insertAt ordered.base attachment.payload
          ordered.rightSlot) :
    (fullyComposedRuleSystem summaryOf domains
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives
        (.side entry.root.control entry.root.cut entry.root.parent) := by
  let edge :
      FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass :=
    {
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.parent
      child := .bounded entry.root.control entry.root.cut
        (.inr entry.localId)
    }
  apply fullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (attachment := domains)
    (I := I) (left := left) (right := right)
    (rightFinal := rightFinal)
    (event := event) (w := w) (j := j) (t := t)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori)
    (intervals := intervals) (macros := macros)
    (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := edge)
  · exact entry.edge_mem
  · apply fullyComposed_localAtom_derives
      (summaryOf := summaryOf) (attachment := domains)
      (I := I) (left := left) (right := right)
      (rightFinal := rightFinal)
      (event := event) (w := w) (j := j) (t := t)
      (edges := edges) (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := ori)
      (intervals := intervals) (macros := macros)
      (wires := wires) (loops := loops)
      (locals := locals) (quotient := quotient)
      (control := entry.root.control)
      (cutValue := entry.root.cut)
      (localId := entry.localId)
    rw [entry.terminal_registered]
    exact
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).decideMismatchRoot_correct.mpr hmismatch

end FiniteMismatchResponseEntry

structure FiniteMismatchResponseRegistry
    [DecidableEq α]
    (sideRoots : List (InitialSideRoot Ctl Cut))
    (edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        Guard LocalId QClass))
    (localTerminal : LocalId → Bool) where
  entry :
    ∀ attachment : ForestWordAttachment α,
      FiniteMismatchResponseEntry attachment sideRoots
        edges localTerminal

namespace FiniteMismatchResponseRegistry

theorem handles_mismatch
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    {sideRoots : List (InitialSideRoot Ctl Cut)}
    {edges :
      List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
        (FirstEventFiniteGuardQuery I left right event w j t)
        LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (registry :
      FiniteMismatchResponseRegistry
        (α := α)
        (Guard :=
          FirstEventFiniteGuardQuery I left right event w j t)
        sideRoots edges localTerminal)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (attachment : ForestWordAttachment α)
    (hmismatch :
      let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      Word.insertAt ordered.base attachment.payload ordered.leftSlot ≠
        Word.insertAt ordered.base attachment.payload
          ordered.rightSlot) :
    ∃ root ∈ sideRoots,
      root.parent = attachment.parent ∧
      (fullyComposedRuleSystem summaryOf domains
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        ).TaggedDerives
          (.side root.control root.cut root.parent) := by
  let entry := registry.entry attachment
  exact ⟨entry.root, entry.root_mem, entry.parent_eq,
    entry.side_derives_of_mismatch
      summaryOf domains I left right rightFinal event w j t
      ctl cut ori intervals macros wires loops locals quotient
      hmismatch⟩

end FiniteMismatchResponseRegistry

end NSSE
