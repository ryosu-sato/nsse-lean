import NSSE.BoundedWordEnumeration
import NSSE.FiniteSemanticRootCompiler
import NSSE.RegisteredAttachmentResponseTable

/-!
# Exact bounded-word avoider atoms

An exact executable avoider test turns every word up to a fixed bound into
one finite local atomic ID.  Selecting all of those bounded tags is sound:
only the IDs whose avoider bit is true derive.
-/

namespace NSSE

universe u

structure ExactAvoiderTest (I : SOAInstance α) where
  test : Word α → Bool
  correct : ∀ word, test word = true ↔ I.Avoider word

def ExactAvoiderTest.ofDecidable
    (I : SOAInstance α)
    [hdecide : ∀ word, Decidable (I.Avoider word)] :
    ExactAvoiderTest I where
  test := fun word => decide (I.Avoider word)
  correct := by
    intro word
    simp

def boundedAvoiderTerminal
    {I : SOAInstance α}
    (test : ExactAvoiderTest I) (bounded : BoundedWord α bound) : Bool :=
  test.test bounded.word

theorem fullyComposed_boundedAvoiderAtom_derives_iff
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (soa : SOAInstance α)
    (avoidTest : ExactAvoiderTest soa)
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      (BoundedWord α bound) QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (alphabet : Enumeration α)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (bounded : BoundedWord α bound) :
    (fullyComposedRuleSystem summaryOf domains
      I left right rightFinal event w j t
      (attachmentResponseTableEnabled edges)
      (boundedAvoiderTerminal avoidTest)
      ctl cut ori intervals macros wires loops
      (boundedWordEnumeration alphabet bound) quotient
      ).TaggedDerives
        (.bounded control cutValue (.inr bounded)) ↔
      soa.Avoider bounded.word := by
  rw [fullyComposed_localAtom_taggedDerives_iff]
  exact avoidTest.correct bounded.word

def boundedAvoiderInitialTags
    (alphabet : Enumeration α) (bound : Nat)
    (control : Ctl) (cut : Cut) :
    List
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard (BoundedWord α bound)) QClass) :=
  (boundedWordEnumeration alphabet bound).values.map fun bounded =>
    .bounded control cut (.inr bounded)

theorem selectedBoundedAvoiderRoot_derives_iff
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (soa : SOAInstance α)
    (avoidTest : ExactAvoiderTest soa)
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      (BoundedWord α bound) QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (alphabet : Enumeration α)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) :
    let system :=
      fullyComposedRuleSystem summaryOf domains
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges)
        (boundedAvoiderTerminal avoidTest)
        ctl cut ori intervals macros wires loops
        (boundedWordEnumeration alphabet bound) quotient
    HornDerives
        (selectedTaggedRootBundle system
          (finiteSemanticRootSelector
            (boundedAvoiderInitialTags
              (Ori := Ori) (Macro := Macro) (Wire := Wire)
              (LoopId := LoopId)
              (Guard :=
                FirstEventFiniteGuardQuery I left right event w j t)
              (QClass := QClass)
              alphabet bound control cutValue))).compiler 1 ↔
      ∃ bounded : BoundedWord α bound,
        soa.Avoider bounded.word := by
  dsimp only
  rw [selectedFiniteSemanticRootBundle_derives_iff]
  constructor
  · rintro ⟨tag, htag, hderive⟩
    simp only [boundedAvoiderInitialTags, List.mem_map] at htag
    obtain ⟨bounded, hbounded, rfl⟩ := htag
    exact ⟨bounded,
      (fullyComposed_boundedAvoiderAtom_derives_iff
        soa avoidTest summaryOf domains I left right rightFinal
        event w j t edges ctl cut ori intervals macros wires loops
        alphabet quotient control cutValue bounded).1 hderive⟩
  · rintro ⟨bounded, havoider⟩
    refine ⟨.bounded control cutValue (.inr bounded), ?_, ?_⟩
    · simp [boundedAvoiderInitialTags,
        (boundedWordEnumeration alphabet bound).complete bounded]
    · exact
        (fullyComposed_boundedAvoiderAtom_derives_iff
          soa avoidTest summaryOf domains I left right rightFinal
          event w j t edges ctl cut ori intervals macros wires loops
          alphabet quotient control cutValue bounded).2 havoider

theorem selectedBoundedAvoiderRoot_derives_iff_exists_word
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (soa : SOAInstance α)
    (avoidTest : ExactAvoiderTest soa)
    (summaryOf : LoopId → LoopSummary Wire)
    (domains : AttachmentDomains)
    (I : AutomataSOAInstance β QC QL QR)
    (left : DFA β QL) (right : DFA β QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent β) (w : Word β) (j t : Nat)
    (edges : List (FiniteAttachmentResponseEdge Ctl Cut Ori Macro
      Wire LoopId
      (FirstEventFiniteGuardQuery I left right event w j t)
      (BoundedWord α bound) QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (alphabet : Enumeration α)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) :
    let system :=
      fullyComposedRuleSystem summaryOf domains
        I left right rightFinal event w j t
        (attachmentResponseTableEnabled edges)
        (boundedAvoiderTerminal avoidTest)
        ctl cut ori intervals macros wires loops
        (boundedWordEnumeration alphabet bound) quotient
    HornDerives
        (selectedTaggedRootBundle system
          (finiteSemanticRootSelector
            (boundedAvoiderInitialTags
              (Ori := Ori) (Macro := Macro) (Wire := Wire)
              (LoopId := LoopId)
              (Guard :=
                FirstEventFiniteGuardQuery I left right event w j t)
              (QClass := QClass)
              alphabet bound control cutValue))).compiler 1 ↔
      ∃ word : Word α, word.length ≤ bound ∧ soa.Avoider word := by
  dsimp only
  have hroot :
      HornDerives
          (selectedTaggedRootBundle
            (fullyComposedRuleSystem summaryOf domains
              I left right rightFinal event w j t
              (attachmentResponseTableEnabled edges)
              (boundedAvoiderTerminal avoidTest)
              ctl cut ori intervals macros wires loops
              (boundedWordEnumeration alphabet bound) quotient)
            (finiteSemanticRootSelector
              (boundedAvoiderInitialTags
                (Ori := Ori) (Macro := Macro) (Wire := Wire)
                (LoopId := LoopId)
                (Guard :=
                  FirstEventFiniteGuardQuery I left right event w j t)
                (QClass := QClass)
                alphabet bound control cutValue))).compiler 1 ↔
        ∃ bounded : BoundedWord α bound,
          soa.Avoider bounded.word := by
    simpa only using
      (selectedBoundedAvoiderRoot_derives_iff
        soa avoidTest summaryOf domains I left right rightFinal
        event w j t edges ctl cut ori intervals macros wires loops
        alphabet quotient control cutValue)
  rw [hroot]
  constructor
  · rintro ⟨bounded, havoider⟩
    exact ⟨bounded.word, bounded.length_le, havoider⟩
  · rintro ⟨word, hlength, havoider⟩
    exact ⟨⟨word, hlength⟩, havoider⟩

end NSSE
