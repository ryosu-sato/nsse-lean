import NSSE.CanonicalRankedStructuralRegistry
import NSSE.FiniteFirstEventHorn

/-!
# A word-independent ranked compiler for profiled first-event responses

The six response solver values are stored in a finite truth profile carried
by the atom.  Consequently the tag type and rule tests do not mention the
concrete automata row, insertion event, source word, or cut positions.
-/

namespace NSSE

def profiledResponseAtomicRuleTests :
    CompilerTagRuleTests Ctl Cut Ori LCA Macro Wire
      ProfiledFirstEventResponse QClass where
  arities := fun _ => []
  terminal := fun kind tag =>
    match kind, tag with
    | .bounded, .bounded _ _ response =>
        profiledFirstEventResponseTerminal response
    | _, _ => false
  enabled := fun _ _ _ => false

def rankedProfiledResponseRuleTests
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass →
        Bool) :
    CompilerTagRuleTests Ctl Cut Ori (SideRank height) Macro
      (FiniteLoopLabel Wire LoopId) ProfiledFirstEventResponse QClass :=
  (finiteLoopRuleTests summaryOf).merge
    ((attachmentResponseRuleTests rankedSideEnabled localEnabled).merge
      profiledResponseAtomicRuleTests)

def rankedProfiledResponseRuleSystem
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass) :
    NumberedRuleSystem
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId ProfiledFirstEventResponse QClass) :=
  (rankedProfiledResponseRuleTests summaryOf height localEnabled).ruleSystem
    ctl cut ori (sideRankEnumeration height) macros
    (FiniteLoopLabel.enumeration wires loops)
    profiledFirstEventResponseEnumeration quotient

def allRankedProfiledResponseTags
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass) (height : Nat) :
    Enumeration
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId ProfiledFirstEventResponse QClass) :=
  CompilerTag.enumeration ctl cut ori (sideRankEnumeration height)
    macros (FiniteLoopLabel.enumeration wires loops)
    profiledFirstEventResponseEnumeration quotient

def exhaustiveProfiledResponseEdges
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass)) :
    List
      (AttachmentResponseEdge Ctl Cut (SideRank height)
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass)) :=
  roots.flatMap fun root =>
    tags.values.map fun child =>
      {
        control := root.control
        cut := root.cut
        parent := root.rank
        child := child
      }

theorem mem_exhaustiveProfiledResponseEdges
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass))
    (root : RankedInitialSideRoot height Ctl Cut)
    (hroot : root ∈ roots)
    (child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId ProfiledFirstEventResponse QClass) :
    ({
      control := root.control
      cut := root.cut
      parent := root.rank
      child := child
    } : AttachmentResponseEdge Ctl Cut (SideRank height)
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId ProfiledFirstEventResponse QClass)) ∈
      exhaustiveProfiledResponseEdges roots tags := by
  simp only [exhaustiveProfiledResponseEdges, List.mem_flatMap,
    List.mem_map]
  exact ⟨root, hroot, child, tags.complete child, rfl⟩

theorem rankedProfiledResponse_atomic_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (response : ProfiledFirstEventResponse)
    (hterminal :
      profiledFirstEventResponseTerminal response = true) :
    (rankedProfiledResponseRuleSystem summaryOf height localEnabled
      ctl cut ori macros wires loops quotient
      ).TaggedDerives (.bounded control cutValue response) := by
  apply NumberedRuleSystem.TaggedDerives.terminal
  change
    (rankedProfiledResponseRuleTests summaryOf height localEnabled
      ).dispatchTerminal (.bounded control cutValue response) = true
  unfold rankedProfiledResponseRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff,
    CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  exact Or.inr (Or.inr (by
    simpa [profiledResponseAtomicRuleTests,
      CompilerTagRuleTests.dispatchTerminal] using hterminal))

theorem rankedProfiledResponse_side_dispatchEnabled
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass →
        Bool)
    (control : Ctl) (cutValue : Cut) (parent : SideRank height)
    (child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId ProfiledFirstEventResponse QClass)
    (henabled : localEnabled control cutValue parent child = true) :
    (rankedProfiledResponseRuleTests summaryOf height localEnabled
      ).dispatchEnabled
        (.side control cutValue parent) [child] = true := by
  unfold rankedProfiledResponseRuleTests
  rw [CompilerTagRuleTests.merge_dispatchEnabled_true_iff,
    CompilerTagRuleTests.merge_dispatchEnabled_true_iff]
  exact Or.inr (Or.inl
    ((attachmentResponse_dispatchEnabled_iff
      rankedSideEnabled localEnabled control cutValue parent [child]).2
      ⟨child, rfl, Or.inr henabled⟩))

theorem rankedProfiledResponse_exhaustive_side_derives
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (height : Nat)
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId ProfiledFirstEventResponse QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (root : RankedInitialSideRoot height Ctl Cut)
    (hroot : root ∈ roots)
    (response : ProfiledFirstEventResponse)
    (hterminal :
      profiledFirstEventResponseTerminal response = true) :
    (rankedProfiledResponseRuleSystem summaryOf height
      (attachmentResponseTableEnabled
        (exhaustiveProfiledResponseEdges roots tags))
      ctl cut ori macros wires loops quotient
      ).TaggedDerives
        (.side root.control root.cut root.rank) := by
  let child :
      FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId ProfiledFirstEventResponse QClass :=
    .bounded root.control root.cut response
  have hchild :
      (rankedProfiledResponseRuleSystem summaryOf height
        (attachmentResponseTableEnabled
          (exhaustiveProfiledResponseEdges roots tags))
        ctl cut ori macros wires loops quotient
        ).TaggedDerives child :=
    rankedProfiledResponse_atomic_derives summaryOf height
      (attachmentResponseTableEnabled
        (exhaustiveProfiledResponseEdges roots tags))
      ctl cut ori macros wires loops quotient
      root.control root.cut response hterminal
  apply NumberedRuleSystem.TaggedDerives.rule (children := [child])
  · simp [rankedProfiledResponseRuleSystem,
      CompilerTagRuleTests.ruleSystem, CompilerTagRuleTests.allArities,
      rankedProfiledResponseRuleTests, CompilerTagRuleTests.merge,
      finiteLoopRuleTests, attachmentResponseRuleTests,
      compilerTagKindEnumeration]
  · apply rankedProfiledResponse_side_dispatchEnabled
      summaryOf height
      (attachmentResponseTableEnabled
        (exhaustiveProfiledResponseEdges roots tags))
    exact
        (attachmentResponseTableEnabled_eq_true_iff
        (exhaustiveProfiledResponseEdges roots tags)
        root.control root.cut root.rank child).2
        (mem_exhaustiveProfiledResponseEdges
          roots tags root hroot child)
  · intro candidate hcandidate
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    exact hchild

end NSSE
