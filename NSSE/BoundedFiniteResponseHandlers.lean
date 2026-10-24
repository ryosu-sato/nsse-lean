import NSSE.BoundedLongForestSideRootExtraction
import NSSE.RegisteredLocalMismatchAtom

/-!
# Finite response registries for a fixed word bound

These registry records are the bounded-interval counterparts of
`FiniteStructuralResponseRegistry` and
`FiniteMismatchResponseRegistry`.  Their selected roots store finite
interval codes while explicitly relating their decoding to the semantic
attachment parent.
-/

namespace NSSE

structure WordBoundedStructuralResponseEntry
    (word : Word α)
    (attachment : ForestWordAttachment α)
    (emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro)
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Label LoopId Guard LocalId QClass))
    (system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori
          (BoundedNatInterval word.length) Macro Label LoopId
          (UnifiedAtomicId Guard LocalId) QClass)) where
  endpoint_ne :
    emitter.singletonChain.finalState ≠ emitter.emitter.sourceState
  root : BoundedInitialSideRoot word.length Ctl Cut
  root_mem : root ∈ sideRoots
  parent_eq : root.parent.toNatInterval = attachment.parent
  child :
    FiniteLoopCompilerTag Ctl Cut Ori (BoundedNatInterval word.length)
      Macro Label LoopId (UnifiedAtomicId Guard LocalId) QClass
  edge_mem :
    ({
      control := root.control
      cut := root.cut
      parent := root.parent
      child := child
    } : BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
      Macro Label LoopId Guard LocalId QClass) ∈ edges
  child_derives : system.TaggedDerives child

namespace WordBoundedStructuralResponseEntry

theorem side_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Label)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    {word : Word α}
    {attachment : ForestWordAttachment α}
    {emitter :
      ContextualStructuralEmitter α ControlWire C letter
        predicateCount Ctl Cut Macro}
    {sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut)}
    {edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Label LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (labels : Enumeration Label) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (entry :
      WordBoundedStructuralResponseEntry word attachment emitter
        sideRoots edges
        (boundedFullyComposedRuleSystem summaryOf domains
          I left right rightFinal event sourceWord j t word.length
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori macros labels loops locals quotient)) :
    (boundedFullyComposedRuleSystem summaryOf domains
      I left right rightFinal event sourceWord j t word.length
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori macros labels loops locals quotient
      ).TaggedDerives
        (.side entry.root.control entry.root.cut entry.root.parent) := by
  apply boundedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (attachment := domains)
    (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := sourceWord)
    (j := j) (t := t) (limit := word.length)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
    (wires := labels) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := {
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.parent
      child := entry.child
    })
  · exact entry.edge_mem
  · exact entry.child_derives

end WordBoundedStructuralResponseEntry

structure WordBoundedStructuralResponseRegistry
    (word : Word α)
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Label LoopId Guard LocalId QClass))
    (system :
      NumberedRuleSystem
        (FiniteLoopCompilerTag Ctl Cut Ori
          (BoundedNatInterval word.length) Macro Label LoopId
          (UnifiedAtomicId Guard LocalId) QClass))
    (C : ControlMonoid ControlWire) (letter : α → ControlWire)
    (predicateCount : Nat) where
  entry :
    ∀ (attachment : ForestWordAttachment α),
      attachment.upper = word →
      ∀ (emitter :
        ContextualStructuralEmitter α ControlWire C letter
          predicateCount Ctl Cut Macro),
      emitter.singletonChain.finalState ≠ emitter.emitter.sourceState →
      WordBoundedStructuralResponseEntry word attachment emitter
        sideRoots edges system

structure WordBoundedMismatchResponseEntry
    [DecidableEq α]
    (word : Word α)
    (attachment : ForestWordAttachment α)
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Wire LoopId Guard LocalId QClass))
    (localTerminal : LocalId → Bool) where
  root : BoundedInitialSideRoot word.length Ctl Cut
  root_mem : root ∈ sideRoots
  parent_eq : root.parent.toNatInterval = attachment.parent
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
    } : BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
      Macro Wire LoopId Guard LocalId QClass) ∈ edges

namespace WordBoundedMismatchResponseEntry

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
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    {word : Word α} {attachment : ForestWordAttachment α}
    {sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut)}
    {edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Wire LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass)}
    {localTerminal : LocalId → Bool}
    (entry :
      WordBoundedMismatchResponseEntry word attachment
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
    (boundedFullyComposedRuleSystem summaryOf domains
      I left right rightFinal event sourceWord j t word.length
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori macros wires loops locals quotient
      ).TaggedDerives
        (.side entry.root.control entry.root.cut entry.root.parent) := by
  apply boundedFullyComposed_registeredResponse_derives
    (summaryOf := summaryOf) (attachment := domains)
    (I := I) (left := left) (right := right)
    (rightFinal := rightFinal) (event := event) (w := sourceWord)
    (j := j) (t := t) (limit := word.length)
    (edges := edges) (localTerminal := localTerminal)
    (ctl := ctl) (cut := cut) (ori := ori) (macros := macros)
    (wires := wires) (loops := loops)
    (locals := locals) (quotient := quotient)
    (edge := {
      control := entry.root.control
      cut := entry.root.cut
      parent := entry.root.parent
      child := .bounded entry.root.control entry.root.cut
        (.inr entry.localId)
    })
  · exact entry.edge_mem
  · apply boundedFullyComposed_localAtom_derives
      (summaryOf := summaryOf) (attachment := domains)
      (I := I) (left := left) (right := right)
      (rightFinal := rightFinal) (event := event) (w := sourceWord)
      (j := j) (t := t) (limit := word.length)
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

end WordBoundedMismatchResponseEntry

structure WordBoundedMismatchResponseRegistry
    [DecidableEq α]
    (word : Word α)
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Wire LoopId Guard LocalId QClass))
    (localTerminal : LocalId → Bool) where
  entry :
    ∀ attachment : ForestWordAttachment α,
      attachment.upper = word →
      WordBoundedMismatchResponseEntry word attachment
        sideRoots edges localTerminal

def wordBoundedLongForestResponseHandlersOfRegistries
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (word : Word α)
    (summaryOf : LoopId → LoopSummary Label)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Label LoopId
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
      WordBoundedStructuralResponseRegistry word sideRoots edges
        (boundedFullyComposedRuleSystem summaryOf domains
          I left right rightFinal event sourceWord j t word.length
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori macros labels loops locals quotient)
        C letter predicateCount)
    (mismatchRegistry :
      WordBoundedMismatchResponseRegistry
        (α := α)
        (Guard :=
          FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
        word sideRoots edges localTerminal) :
    WordBoundedLongForestResponseHandlers word
      (boundedFullyComposedRuleSystem summaryOf domains
        I left right rightFinal event sourceWord j t word.length
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros labels loops locals quotient)
      sideRoots C letter predicateCount where
  structural := by
    intro attachment hupper emitter hendpoint
    let entry :=
      structuralRegistry.entry attachment hupper emitter hendpoint
    exact ⟨entry.root, entry.root_mem, entry.parent_eq,
      entry.side_derives summaryOf domains I left right rightFinal
        event sourceWord j t ctl cut ori macros labels loops locals
        quotient⟩
  mismatch := by
    intro attachment hupper hmismatch
    let entry := mismatchRegistry.entry attachment hupper
    exact ⟨entry.root, entry.root_mem, entry.parent_eq,
      entry.side_derives_of_mismatch summaryOf domains I left right
        rightFinal event sourceWord j t ctl cut ori macros labels
        loops locals quotient hmismatch⟩

theorem wordBoundedRegistries_extract_from_long_forest
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Label] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (word : Word α) (heightBound : Nat)
    (summaryOf : LoopId → LoopSummary Label)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t : Nat)
    (sideRoots :
      List (BoundedInitialSideRoot word.length Ctl Cut))
    (edges :
      List
        (BoundedFiniteAttachmentResponseEdge word.length Ctl Cut Ori
          Macro Label LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (labels : Enumeration Label) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId) (quotient : Enumeration QClass)
    (C : ControlMonoid ControlWire)
    (letter : α → ControlWire)
    (predicates : List UnaryArithmeticPredicate)
    (structuralRegistry :
      WordBoundedStructuralResponseRegistry word sideRoots edges
        (boundedFullyComposedRuleSystem summaryOf domains
          I left right rightFinal event sourceWord j t word.length
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori macros labels loops locals quotient)
        C letter predicates.length)
    (mismatchRegistry :
      WordBoundedMismatchResponseRegistry
        (α := α)
        (Guard :=
          FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
        word sideRoots edges localTerminal)
    (forest :
      FactorTree.HeightBoundedForest C letter word heightBound)
    (hlong : 2 ^ heightBound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (wireOf : NatInterval → ControlWire)
    (strongWire : ControlWire)
    (control : Ctl) (cutValue : Cut) (macroData : Macro) :
    ∃ root ∈ sideRoots,
      (boundedFullyComposedRuleSystem summaryOf domains
        I left right rightFinal event sourceWord j t word.length
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros labels loops locals quotient
        ).TaggedDerives
          (.side root.control root.cut root.parent) := by
  let handlers :=
    wordBoundedLongForestResponseHandlersOfRegistries
      word summaryOf domains I left right rightFinal event sourceWord j t
      sideRoots edges localTerminal ctl cut ori macros labels loops
      locals quotient C letter predicates.length
      structuralRegistry mismatchRegistry
  exact handlers.extract_from_long_forest forest hlong
    payload hpayload intervalChildren wireOf strongWire
    control cutValue macroData

end NSSE
