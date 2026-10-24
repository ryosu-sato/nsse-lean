import NSSE.SemanticTaggedRootFamily

/-!
# Finite compiler for selected attachment roots

This module combines the executable response-edge table with the
executable initial-side-root selector.  Its Horn super-root exposes
exactly the selected attachment roots, never every compiler state.
-/

namespace NSSE

universe u

theorem finiteAttachmentRootCompiler_derives_iff
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
    (roots : List (InitialSideRoot Ctl Cut)) :
    let system :=
      fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori intervals macros wires loops locals quotient
    HornDerives
        (selectedTaggedRootBundle system
          (initialSideRootSelector roots)).compiler 1 ↔
      ∃ root ∈ roots, ∃ child,
        (intervalSideEnabled attachment
            root.control root.cut root.parent child = true ∨
          ({
            control := root.control
            cut := root.cut
            parent := root.parent
            child := child
          } : FiniteAttachmentResponseEdge Ctl Cut Ori Macro Wire LoopId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId QClass) ∈ edges) ∧
        system.TaggedDerives child := by
  dsimp only
  rw [selectedInitialSideRootBundle_derives_iff]
  constructor
  · rintro ⟨root, hroot, hderive⟩
    obtain ⟨child, hresponse, hchild⟩ :=
      (fullyComposed_table_side_taggedDerives_iff
        summaryOf attachment I left right rightFinal event w j t
        edges localTerminal ctl cut ori intervals macros wires loops
        locals quotient root.control root.cut root.parent).1 hderive
    exact ⟨root, hroot, child, hresponse, hchild⟩
  · rintro ⟨root, hroot, child, hresponse, hchild⟩
    refine ⟨root, hroot, ?_⟩
    exact
      (fullyComposed_table_side_taggedDerives_iff
        summaryOf attachment I left right rightFinal event w j t
        edges localTerminal ctl cut ori intervals macros wires loops
        locals quotient root.control root.cut root.parent).2
        ⟨child, hresponse, hchild⟩

end NSSE
