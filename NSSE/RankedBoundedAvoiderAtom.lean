import NSSE.BoundedAvoiderAtom
import NSSE.RankedAttachmentResponseDispatcher

/-!
# Exact bounded-word roots in the ranked compiler
-/

namespace NSSE

def rankedBoundedAvoiderInitialTags
    (alphabet : Enumeration α) (bound height : Nat)
    (control : Ctl) (cut : Cut) :
    List
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId
        (UnifiedAtomicId Guard (BoundedWord α bound)) QClass) :=
  (boundedWordEnumeration alphabet bound).values.map fun bounded =>
    .bounded control cut (.inr bounded)

theorem rankedFullyComposed_boundedAvoiderAtom_derives_iff
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (soa : SOAInstance α)
    (avoidTest : ExactAvoiderTest soa)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t height : Nat)
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          (BoundedWord α bound) QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (alphabet : Enumeration α) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (bounded : BoundedWord α bound) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event sourceWord j t height
      (attachmentResponseTableEnabled edges)
      (boundedAvoiderTerminal avoidTest)
      ctl cut ori macros wires loops
      (boundedWordEnumeration alphabet bound) quotient
      ).TaggedDerives
        (.bounded control cutValue (.inr bounded)) ↔
      soa.Avoider bounded.word := by
  rw [rankedFullyComposed_localAtom_taggedDerives_iff]
  exact avoidTest.correct bounded.word

theorem rankedBoundedAvoiderRoots_exact
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (soa : SOAInstance α)
    (avoidTest : ExactAvoiderTest soa)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t height : Nat)
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          (BoundedWord α bound) QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (alphabet : Enumeration α) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) :
    let system :=
      rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges)
        (boundedAvoiderTerminal avoidTest)
        ctl cut ori macros wires loops
        (boundedWordEnumeration alphabet bound) quotient
    (∃ state ∈
        rankedBoundedAvoiderInitialTags
          (Ori := Ori) (Macro := Macro) (Wire := Wire)
          (LoopId := LoopId)
          (Guard :=
            FirstEventFiniteGuardQuery I left right event sourceWord j t)
          (QClass := QClass)
          alphabet bound height control cutValue,
        system.TaggedDerives state) ↔
      ∃ word : Word α,
        word.length ≤ bound ∧ soa.Avoider word := by
  dsimp only
  constructor
  · rintro ⟨state, hstate, hderive⟩
    simp only [rankedBoundedAvoiderInitialTags, List.mem_map] at hstate
    obtain ⟨bounded, hbounded, rfl⟩ := hstate
    exact ⟨bounded.word, bounded.length_le,
      (rankedFullyComposed_boundedAvoiderAtom_derives_iff
        soa avoidTest summaryOf I left right rightFinal event sourceWord
        j t height edges ctl cut ori macros wires loops alphabet quotient
        control cutValue bounded).1 hderive⟩
  · rintro ⟨word, hlength, havoider⟩
    let bounded : BoundedWord α bound := ⟨word, hlength⟩
    refine ⟨.bounded control cutValue (.inr bounded), ?_, ?_⟩
    · simp [rankedBoundedAvoiderInitialTags,
        (boundedWordEnumeration alphabet bound).complete bounded]
    · exact
        (rankedFullyComposed_boundedAvoiderAtom_derives_iff
          soa avoidTest summaryOf I left right rightFinal event
          sourceWord j t height edges ctl cut ori macros wires loops
          alphabet quotient control cutValue bounded).2 havoider

def rankedEncodedBoundedAvoiderInitialTags
    (alphabet : Enumeration α) (bound height : Nat)
    (control : Ctl) (cut : Cut)
    (encode : BoundedWord α bound → LocalId) :
    List
      (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
        Macro Wire LoopId (UnifiedAtomicId Guard LocalId) QClass) :=
  (boundedWordEnumeration alphabet bound).values.map fun bounded =>
    .bounded control cut (.inr (encode bounded))

theorem rankedEncodedBoundedAvoiderRoots_exact
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (soa : SOAInstance α)
    (avoidTest : ExactAvoiderTest soa)
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (sourceWord : Word β) (j t height : Nat)
    (edges :
      List
        (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
          Wire LoopId
          (FirstEventFiniteGuardQuery I left right
            event sourceWord j t)
          LocalId QClass))
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (locals : Enumeration LocalId)
    (alphabet : Enumeration α) (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (encode : BoundedWord α bound → LocalId)
    (encode_terminal :
      ∀ bounded,
        localTerminal (encode bounded) =
          boundedAvoiderTerminal avoidTest bounded) :
    let system :=
      rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros wires loops locals quotient
    (∃ state ∈
        rankedEncodedBoundedAvoiderInitialTags
          (Ori := Ori) (Macro := Macro) (Wire := Wire)
          (LoopId := LoopId)
          (Guard :=
            FirstEventFiniteGuardQuery I left right event sourceWord j t)
          (QClass := QClass)
          alphabet bound height control cutValue encode,
        system.TaggedDerives state) ↔
      ∃ word : Word α,
        word.length ≤ bound ∧ soa.Avoider word := by
  dsimp only
  constructor
  · rintro ⟨state, hstate, hderive⟩
    simp only [rankedEncodedBoundedAvoiderInitialTags,
      List.mem_map] at hstate
    obtain ⟨bounded, hbounded, rfl⟩ := hstate
    have hterminal :=
      (rankedFullyComposed_localAtom_taggedDerives_iff
        summaryOf I left right rightFinal event sourceWord j t height
        (attachmentResponseTableEnabled edges) localTerminal
        ctl cut ori macros wires loops locals quotient
        control cutValue (encode bounded)).1 hderive
    rw [encode_terminal bounded] at hterminal
    exact ⟨bounded.word, bounded.length_le,
      (avoidTest.correct bounded.word).1 hterminal⟩
  · rintro ⟨word, hlength, havoider⟩
    let bounded : BoundedWord α bound := ⟨word, hlength⟩
    refine ⟨.bounded control cutValue (.inr (encode bounded)), ?_, ?_⟩
    · simp only [rankedEncodedBoundedAvoiderInitialTags,
        List.mem_map]
      exact ⟨bounded,
        (boundedWordEnumeration alphabet bound).complete bounded, rfl⟩
    · apply
        (rankedFullyComposed_localAtom_taggedDerives_iff
          summaryOf I left right rightFinal event sourceWord j t height
          (attachmentResponseTableEnabled edges) localTerminal
          ctl cut ori macros wires loops locals quotient
          control cutValue (encode bounded)).2
      rw [encode_terminal bounded]
      exact (avoidTest.correct bounded.word).2 havoider

end NSSE
