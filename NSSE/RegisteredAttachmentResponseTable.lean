import NSSE.AttachmentResponseDispatcher

/-!
# Executable finite registration of attachment responses

A fixed compiler records every local attachment response as one edge from
its side root context to the emitted child tag.  The edge list is finite,
and membership in that list is the executable `localEnabled` predicate
used by the fully composed dispatcher.
-/

namespace NSSE

universe u uCtl uCut uParent uChild

structure AttachmentResponseEdge
    (Ctl : Type uCtl) (Cut : Type uCut)
    (Parent : Type uParent) (Child : Type uChild) where
  control : Ctl
  cut : Cut
  parent : Parent
  child : Child
deriving DecidableEq

def attachmentResponseTableEnabled
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Parent] [DecidableEq Child]
    (edges : List (AttachmentResponseEdge Ctl Cut Parent Child))
    (control : Ctl) (cut : Cut) (parent : Parent) (child : Child) :
    Bool :=
  decide ({
    control := control
    cut := cut
    parent := parent
    child := child
  } ∈ edges)

@[simp] theorem attachmentResponseTableEnabled_eq_true_iff
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Parent] [DecidableEq Child]
    (edges : List (AttachmentResponseEdge Ctl Cut Parent Child))
    (control : Ctl) (cut : Cut) (parent : Parent) (child : Child) :
    attachmentResponseTableEnabled edges control cut parent child = true ↔
      ({
        control := control
        cut := cut
        parent := parent
        child := child
      } : AttachmentResponseEdge Ctl Cut Parent Child) ∈ edges := by
  simp [attachmentResponseTableEnabled]

@[simp] theorem attachmentResponseTableEnabled_singleton
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq Parent] [DecidableEq Child]
    (edge : AttachmentResponseEdge Ctl Cut Parent Child) :
    attachmentResponseTableEnabled [edge]
        edge.control edge.cut edge.parent edge.child = true := by
  simp

abbrev FiniteAttachmentResponseEdge
    (Ctl Cut Ori Macro Wire LoopId Guard LocalId QClass : Type) :=
  AttachmentResponseEdge Ctl Cut NatInterval
    (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
      (UnifiedAtomicId Guard LocalId) QClass)

theorem fullyComposed_table_side_taggedDerives_iff
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
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (parent : NatInterval) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives (.side control cutValue parent) ↔
      ∃ child,
        (intervalSideEnabled attachment control cutValue parent child =
            true ∨
          ({
            control := control
            cut := cutValue
            parent := parent
            child := child
          } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId QClass) ∈ edges) ∧
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori intervals macros wires loops locals quotient
          ).TaggedDerives child := by
  rw [fullyComposed_side_taggedDerives_iff]
  simp only [attachmentResponseTableEnabled_eq_true_iff]

theorem fullyComposed_registeredResponse_derives
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
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (edge : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass)
    (hregistered : edge ∈ edges)
    (hchild :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros wires loops locals quotient
        ).TaggedDerives edge.child) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives (.side edge.control edge.cut edge.parent) := by
  rw [fullyComposed_table_side_taggedDerives_iff]
  exact ⟨edge.child, Or.inr hregistered, hchild⟩

theorem fullyComposed_structural_derives_of_nonidentity
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
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (tag : FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass)
    (loopId : LoopId) (hloop : tag.loopId? = some loopId)
    (hnonidentity : ¬ IdentityLoop (summaryOf loopId)) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives tag := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ).dispatchTerminal tag = true
  unfold fullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  apply Or.inl
  exact (finiteLoop_dispatchTerminal_iff summaryOf tag).2
    ⟨loopId, hloop, hnonidentity⟩

theorem fullyComposed_localAtom_derives
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
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (localId : LocalId)
    (hterminal : localTerminal localId = true) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives (.bounded control cutValue (.inr localId)) := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (fullyComposedRuleTests summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ).dispatchTerminal (.bounded control cutValue (.inr localId)) = true
  unfold fullyComposedRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  exact Or.inr (Or.inr (by
    simpa [unifiedAtomicRuleTests,
      CompilerTagRuleTests.dispatchTerminal] using hterminal))

theorem fullyComposed_localAtom_taggedDerives_iff
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
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (localId : LocalId) :
    (fullyComposedRuleSystem summaryOf attachment
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges) localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      ).TaggedDerives (.bounded control cutValue (.inr localId)) ↔
      localTerminal localId = true := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal =>
        change
          (fullyComposedRuleTests summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled edges) localTerminal
            ).dispatchTerminal
              (.bounded control cutValue (.inr localId)) = true
          at hterminal
        simpa [fullyComposedRuleTests,
          CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
          finiteLoopRuleTests, attachmentResponseRuleTests,
          unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchTerminal,
          CompilerTag.loopId?, CompilerTag.kind] using hterminal
    | @rule _ children harity henabled hchildren =>
        change
          (fullyComposedRuleTests summaryOf attachment
            I left right rightFinal event w j t
            (attachmentResponseTableEnabled edges) localTerminal
            ).dispatchEnabled
              (.bounded control cutValue (.inr localId)) children = true
          at henabled
        simp [fullyComposedRuleTests,
          CompilerTagRuleTests.merge,
          finiteLoopRuleTests, attachmentResponseRuleTests,
          unifiedAtomicRuleTests,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTag.loopId?, CompilerTag.kind] at henabled
  · exact fullyComposed_localAtom_derives
      summaryOf attachment I left right rightFinal event w j t
      edges localTerminal ctl cut ori intervals macros wires loops
      locals quotient control cutValue localId

end NSSE
