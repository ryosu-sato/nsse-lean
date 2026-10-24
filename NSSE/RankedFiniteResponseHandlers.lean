import NSSE.RankedLongForestSideRootExtraction
import NSSE.RegisteredLocalMismatchAtom

/-!
# Structural and mismatch registries over a fixed rank alphabet
-/

namespace NSSE

structure RankedStructuralResponseEntry
    (height : Nat)
    (realizes : SideRank height → NatInterval → Prop)
    (attachment : ForestWordAttachment α)
    (emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro)
    (sideRoots : List (RankedInitialSideRoot height Ctl Cut))
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Label LoopId Guard LocalId QClass))
    (system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Label LoopId (UnifiedAtomicId Guard LocalId) QClass)) where
  endpoint_ne :
    emitter.singletonChain.finalState ≠ emitter.emitter.sourceState
  root : RankedInitialSideRoot height Ctl Cut
  root_mem : root ∈ sideRoots
  root_realizes : realizes root.rank attachment.parent
  child :
    FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
      Macro Label LoopId (UnifiedAtomicId Guard LocalId) QClass
  edge_mem :
    ({
      control := root.control
      cut := root.cut
      parent := root.rank
      child := child
    } : RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
      Label LoopId Guard LocalId QClass) ∈ edges
  child_derives : system.TaggedDerives child

namespace RankedStructuralResponseEntry

theorem side_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Label)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    {height : Nat}
    {realizes : SideRank height → NatInterval → Prop}
    {attachment : ForestWordAttachment α}
    {emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro}
    {sideRoots : List (RankedInitialSideRoot height Ctl Cut)}
    {edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Label LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (labels : Enumeration Label) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (entry :
      RankedStructuralResponseEntry height realizes attachment emitter
        sideRoots edges
        (rankedFullyComposedRuleSystem summaryOf
          I left right rightFinal event sourceWord j t height
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori macros labels loops locals quotient)) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event sourceWord j t height
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori macros labels loops locals quotient
      ).TaggedDerives
        (.side entry.root.control entry.root.cut entry.root.rank) := by
  apply rankedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := sourceWord)
    (j := j) (t := t) (height := height)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
    (wires := labels) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := {
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.rank
      child := entry.child
    })
  · exact entry.edge_mem
  · exact entry.child_derives

end RankedStructuralResponseEntry

structure RankedStructuralResponseRegistry
    (height : Nat)
    (realizes : SideRank height → NatInterval → Prop)
    (sideRoots : List (RankedInitialSideRoot height Ctl Cut))
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Label LoopId Guard LocalId QClass))
    (system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Label LoopId (UnifiedAtomicId Guard LocalId) QClass))
    (C : ControlMonoid ControlWire) (letter : α → ControlWire)
    (predicateCount : Nat) where
  entry :
    ∀ (attachment : ForestWordAttachment α)
      (emitter :
        ContextualStructuralEmitter α ControlWire C letter
          predicateCount Ctl Cut Macro),
      emitter.singletonChain.finalState ≠ emitter.emitter.sourceState →
      RankedStructuralResponseEntry height realizes attachment emitter
        sideRoots edges system

structure RankedMismatchResponseEntry
    [DecidableEq α]
    (height : Nat)
    (realizes : SideRank height → NatInterval → Prop)
    (attachment : ForestWordAttachment α)
    (sideRoots : List (RankedInitialSideRoot height Ctl Cut))
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (localTerminal : LocalId → Bool) where
  root : RankedInitialSideRoot height Ctl Cut
  root_mem : root ∈ sideRoots
  root_realizes : realizes root.rank attachment.parent
  localId : LocalId
  terminal_registered :
    localTerminal localId =
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).mismatchTerminal
  edge_mem :
    ({
      control := root.control
      cut := root.cut
      parent := root.rank
      child := .bounded root.control root.cut (.inr localId)
    } : RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
      Wire LoopId Guard LocalId QClass) ∈ edges

namespace RankedMismatchResponseEntry

theorem side_derives_of_mismatch
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    {height : Nat}
    {realizes : SideRank height → NatInterval → Prop}
    {attachment : ForestWordAttachment α}
    {sideRoots : List (RankedInitialSideRoot height Ctl Cut)}
    {edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (entry :
      RankedMismatchResponseEntry height realizes attachment
        sideRoots edges localTerminal)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (hmismatch :
      let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      Word.insertAt ordered.base attachment.payload ordered.leftSlot ≠
        Word.insertAt ordered.base attachment.payload
          ordered.rightSlot) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event sourceWord j t height
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives
        (.side entry.root.control entry.root.cut entry.root.rank) := by
  apply rankedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := sourceWord)
    (j := j) (t := t) (height := height)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
    (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := {
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.rank
      child := .bounded entry.root.control entry.root.cut
        (.inr entry.localId)
    })
  · exact entry.edge_mem
  · apply rankedFullyComposed_localAtom_derives
      (summaryOf := summaryOf) (I := I)
      (left := left) (right := right) (rightFinal := rightFinal)
      (event := event) (w := sourceWord) (j := j) (t := t)
      (height := height)
      (localEnabled := attachmentResponseTableEnabled edges)
      (localTerminal := localTerminal)
      (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
      (wires := wires) (loops := loops)
      (locals := locals) (quotient := quotient)
      (control := entry.root.control) (cutValue := entry.root.cut)
      (localId := entry.localId)
    rw [entry.terminal_registered]
    exact
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).decideMismatchRoot_correct.mpr hmismatch

end RankedMismatchResponseEntry

structure RankedMismatchResponseRegistry
    [DecidableEq α]
    (height : Nat)
    (realizes : SideRank height → NatInterval → Prop)
    (sideRoots : List (RankedInitialSideRoot height Ctl Cut))
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId Guard LocalId QClass))
    (localTerminal : LocalId → Bool) where
  entry :
    ∀ attachment : ForestWordAttachment α,
      RankedMismatchResponseEntry height realizes attachment
        sideRoots edges localTerminal

def rankedLongForestResponseHandlersOfRegistries
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (height : Nat)
    (realizes : SideRank height → NatInterval → Prop)
    (summaryOf : LoopId → LoopSummary Label)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (sideRoots : List (RankedInitialSideRoot height Ctl Cut))
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Label LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (labels : Enumeration Label) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (C : ControlMonoid ControlWire) (letter : α → ControlWire)
    (predicateCount : Nat)
    (structuralRegistry :
      RankedStructuralResponseRegistry height realizes sideRoots edges
        (rankedFullyComposedRuleSystem summaryOf
          I left right rightFinal event sourceWord j t height
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori macros labels loops locals quotient)
        C letter predicateCount)
    (mismatchRegistry :
      RankedMismatchResponseRegistry
        (α := α)
        (Guard :=
          FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
        height realizes sideRoots edges localTerminal) :
    RankedLongForestResponseHandlers height
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros labels loops locals quotient)
      sideRoots realizes C letter predicateCount where
  structural := by
    intro attachment emitter hendpoint
    let entry := structuralRegistry.entry attachment emitter hendpoint
    exact ⟨entry.root, entry.root_mem, entry.root_realizes,
      entry.side_derives summaryOf I left right rightFinal event
        sourceWord j t ctl cut ori macros labels loops locals quotient⟩
  mismatch := by
    intro attachment hmismatch
    let entry := mismatchRegistry.entry attachment
    exact ⟨entry.root, entry.root_mem, entry.root_realizes,
      entry.side_derives_of_mismatch summaryOf I left right rightFinal
        event sourceWord j t ctl cut ori macros labels loops locals
        quotient hmismatch⟩

end NSSE
