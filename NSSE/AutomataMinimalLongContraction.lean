import NSSE.AutomataMinimalContractionData
import NSSE.FiniteTransformationMonoid
import NSSE.GroupPaletteFactorForest
import NSSE.LongForestIdempotentNode
import NSSE.IdempotentNodeAttachment

/-!
# Uniform candidate-aligned contraction of long minimal avoiders

The uniform Simon forest is instantiated with the transformation monoid
of the candidate DFA.  Hence an idempotent node supplies a deletion that
preserves candidate acceptance, rather than merely an unrelated control
value.
-/

namespace NSSE

universe u

theorem AutomataSOAInstance.exists_uniform_long_contractionData
    [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ shorter,
          I.toSOA.candidate shorter ∧
          shorter.length < word.length ∧
          ∃ index : Fin I.toSOA.rows.length,
            I.toSOA.IndexedRootQuery index shorter := by
  classical
  obtain ⟨heightBound, uniform⟩ :=
    exists_uniformFactorForestBound
      (transformationMonoid QC)
      (I.candidate.transformationEnumeration candidateStates)
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  have hword : word ≠ [] := by
    intro hempty
    subst word
    simp at hlong
  let forest :=
    Classical.choice
      (uniform.forest I.candidate.letterTransform word hword)
  obtain ⟨left, right, children, value, hdecompose,
      hcount, hchildren, hidempotent, hcontrols⟩ :=
    forest.exists_idempotent_context hlong
  cases children with
  | nil =>
      simp at hcount
  | cons first tail =>
      cases tail with
      | nil =>
          simp at hcount
      | cons second tail =>
          cases tail with
          | nil =>
              simp at hcount
          | cons third rest =>
              have hminimal' :
                  I.toSOA.LengthMinimalAvoider
                    (left ++
                      FactorTree.forestYield
                        ([first] ++ second :: (third :: rest)) ++
                      right) := by
                rw [hdecompose] at hminimal
                simpa using hminimal
              obtain ⟨_hdelete, hcandidate, hshort, hquery⟩ :=
                I.idempotent_child_contractionData
                  (before := [first])
                  (deleted := second)
                  (after := third :: rest)
                  (e := value)
                  hidempotent
                  (by
                    intro tree htree
                    apply hcontrols
                    simpa using htree)
                  (by simp)
                  (FactorTree.isForest_wellFormed
                    (transformationMonoid QC)
                    I.candidate.letterTransform
                    (hchildren second (by simp)))
                  left right hminimal'
              refine ⟨left ++
                  FactorTree.forestYield ([first] ++ third :: rest) ++
                  right,
                hcandidate, ?_, hquery⟩
              simpa [hdecompose] using hshort

structure CandidateAlignedAttachedContraction
    (I : AutomataSOAInstance α QC QL QR)
    (word : Word α) where
  shorter : Word α
  attachment : ForestWordAttachment α
  upper_eq : attachment.upper = shorter
  middle_ne_nil :
    attachment.toIntervalWordAttachment.orderedAttachment.middle ≠ []
  deleted : FactorTree α
  payload_eq : attachment.payload = deleted.yield
  deleted_wellFormed : deleted.WellFormed
  leftInsertionCandidate :
    I.toSOA.candidate
      (attachment.left ++
        Word.insertAt
          attachment.toIntervalWordAttachment.orderedAttachment.base
          attachment.payload
          attachment.toIntervalWordAttachment.orderedAttachment.leftSlot ++
        attachment.right)
  rightInsertionCandidate :
    I.toSOA.candidate
      (attachment.left ++
        Word.insertAt
          attachment.toIntervalWordAttachment.orderedAttachment.base
          attachment.payload
          attachment.toIntervalWordAttachment.orderedAttachment.rightSlot ++
        attachment.right)
  rightInsertion_eq_word :
    attachment.left ++
        Word.insertAt
          attachment.toIntervalWordAttachment.orderedAttachment.base
          attachment.payload
          attachment.toIntervalWordAttachment.orderedAttachment.rightSlot ++
      attachment.right = word
  deletesTo : I.toSOA.DeletesTo shorter word
  candidate : I.toSOA.candidate shorter
  shorter_length : shorter.length < word.length
  index : Fin I.toSOA.rows.length
  query : I.toSOA.IndexedRootQuery index shorter

theorem AutomataSOAInstance.exists_uniform_long_attachedContraction
    [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        Nonempty
          (CandidateAlignedAttachedContraction
            I word) := by
  classical
  obtain ⟨heightBound, uniform⟩ :=
    exists_uniformFactorForestBound
      (transformationMonoid QC)
      (I.candidate.transformationEnumeration candidateStates)
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  have hword : word ≠ [] := by
    intro hempty
    subst word
    simp at hlong
  let forest :=
    Classical.choice
      (uniform.forest I.candidate.letterTransform word hword)
  obtain ⟨left, right, children, value, hdecompose,
      hcount, hchildren, hidempotent, hcontrols⟩ :=
    forest.exists_idempotent_context hlong
  cases children with
  | nil =>
      simp at hcount
  | cons first tail =>
      cases tail with
      | nil =>
          simp at hcount
      | cons second tail =>
          cases tail with
          | nil =>
              simp at hcount
          | cons third rest =>
              have hminimal' :
                  I.toSOA.LengthMinimalAvoider
                    (left ++
                      FactorTree.forestYield
                        ([first] ++ second :: (third :: rest)) ++
                      right) := by
                rw [hdecompose] at hminimal
                simpa using hminimal
              obtain ⟨hdelete, hcandidate, hshort, index, hquery⟩ :=
                I.idempotent_child_contractionData
                  (before := [first])
                  (deleted := second)
                  (after := third :: rest)
                  (e := value)
                  hidempotent
                  (by
                    intro tree htree
                    apply hcontrols
                    simpa using htree)
                  (by simp)
                  (FactorTree.isForest_wellFormed
                    (transformationMonoid QC)
                    I.candidate.letterTransform
                    (hchildren second (by simp)))
                  left right hminimal'
              have hfirst :=
                FactorTree.isForest_wellFormed
                  (transformationMonoid QC)
                  I.candidate.letterTransform
                  (hchildren first (by simp))
              have hsecond :=
                FactorTree.isForest_wellFormed
                  (transformationMonoid QC)
                  I.candidate.letterTransform
                  (hchildren second (by simp))
              have hthird :=
                FactorTree.isForest_wellFormed
                  (transformationMonoid QC)
                  I.candidate.letterTransform
                  (hchildren third (by simp))
              let two : TwoForestAttachment α := {
                left := left
                forest := first :: third :: rest
                right := right
                payload := second.yield
                payload_nonempty := hsecond
                first := {
                  before := []
                  child := first
                  after := third :: rest
                  decomposition := rfl
                  wellFormed := hfirst
                }
                second := {
                  before := [first]
                  child := third
                  after := rest
                  decomposition := rfl
                  wellFormed := hthird
                }
              }
              let attachment := two.toForestWordAttachment
              have hbase :
                  (attachment.toIntervalWordAttachment.orderedAttachment
                    ).base =
                    FactorTree.forestYield (first :: third :: rest) :=
                attachment.parentWord_eq_forestYield
              have hleftSlot :
                  (attachment.toIntervalWordAttachment.orderedAttachment
                    ).leftSlot = 0 := by
                simp [attachment, two,
                  IntervalWordAttachment.orderedAttachment,
                  IntervalWordAttachment.leftSlot,
                  IntervalWordAttachment.firstLocalStart,
                  IntervalWordAttachment.secondLocalStart,
                  TwoForestAttachment.toForestWordAttachment,
                  TwoForestAttachment.domains, ForestOccurrence.interval,
                  forestChildInterval,
                  ForestWordAttachment.toIntervalWordAttachment,
                  ForestWordAttachment.parent, forestParentInterval,
                  FactorTree.forestYield]
              have hrightSlot :
                  (attachment.toIntervalWordAttachment.orderedAttachment
                    ).rightSlot = first.yield.length := by
                simp [attachment, two,
                  IntervalWordAttachment.orderedAttachment,
                  IntervalWordAttachment.rightSlot,
                  IntervalWordAttachment.firstLocalStart,
                  IntervalWordAttachment.secondLocalStart,
                  TwoForestAttachment.toForestWordAttachment,
                  TwoForestAttachment.domains, ForestOccurrence.interval,
                  forestChildInterval,
                  ForestWordAttachment.toIntervalWordAttachment,
                  ForestWordAttachment.parent, forestParentInterval,
                  FactorTree.forestYield]
                omega
              have hallRetained :
                  ∀ tree ∈ first :: third :: rest,
                    FactorTree.control (transformationMonoid QC)
                      I.candidate.letterTransform tree = value := by
                intro tree htree
                apply hcontrols
                simp only [List.mem_cons] at htree ⊢
                rcases htree with hfirstTree | hthirdTree | hrest
                · exact Or.inl hfirstTree
                · exact Or.inr (Or.inr (Or.inl hthirdTree))
                · exact Or.inr (Or.inr (Or.inr hrest))
              have hleftControl :
                  I.candidate.transitionEval
                      (FactorTree.forestYield (first :: third :: rest)) =
                    I.candidate.transitionEval
                      (FactorTree.forestYield
                        (second :: first :: third :: rest)) := by
                exact FactorTree.idempotent_sibling_replacement
                  (transformationMonoid QC)
                  I.candidate.letterTransform hidempotent
                  hallRetained
                  (by
                    intro tree htree
                    apply hcontrols
                    simp only [List.mem_cons] at htree ⊢
                    rcases htree with hsecondTree | hfirstTree |
                        hthirdTree | hrest
                    · exact Or.inr (Or.inl hsecondTree)
                    · exact Or.inl hfirstTree
                    · exact Or.inr (Or.inr (Or.inl hthirdTree))
                    · exact Or.inr (Or.inr (Or.inr hrest)))
                  (by simp) (by simp)
              have hrightControl :
                  I.candidate.transitionEval
                      (FactorTree.forestYield (first :: third :: rest)) =
                    I.candidate.transitionEval
                      (FactorTree.forestYield
                        (first :: second :: third :: rest)) := by
                exact FactorTree.idempotent_sibling_replacement
                  (transformationMonoid QC)
                  I.candidate.letterTransform hidempotent
                  hallRetained hcontrols (by simp) (by simp)
              let shorter :=
                left ++ FactorTree.forestYield (first :: third :: rest) ++
                  right
              refine ⟨{
                shorter := shorter
                attachment := attachment
                upper_eq := by rfl
                middle_ne_nil := ?_
                deleted := second
                payload_eq := rfl
                deleted_wellFormed := hsecond
                leftInsertionCandidate := ?_
                rightInsertionCandidate := ?_
                rightInsertion_eq_word := ?_
                deletesTo := ?_
                candidate := hcandidate
                shorter_length := ?_
                index := index
                query := hquery
              }⟩
              · intro hempty
                have hmiddle :=
                  (attachment.toIntervalWordAttachment.orderedAttachment
                    ).middle_length
                rw [hempty, hleftSlot, hrightSlot] at hmiddle
                simp only [List.length_nil] at hmiddle
                have hpositive : 0 < first.yield.length :=
                  List.length_pos_iff.mpr hfirst
                omega
              · have hc :=
                  (I.candidate.accepts_context_replace
                    left (FactorTree.forestYield (first :: third :: rest))
                    (FactorTree.forestYield
                      (second :: first :: third :: rest))
                    right hleftControl).1 hcandidate
                change I.toSOA.candidate
                  (left ++ Word.insertAt
                    (attachment.toIntervalWordAttachment.orderedAttachment
                      ).base second.yield
                    (attachment.toIntervalWordAttachment.orderedAttachment
                      ).leftSlot ++ right)
                rw [hbase, hleftSlot]
                simpa [Word.insertAt, FactorTree.forestYield] using hc
              · have hc :=
                  (I.candidate.accepts_context_replace
                    left (FactorTree.forestYield (first :: third :: rest))
                    (FactorTree.forestYield
                      (first :: second :: third :: rest))
                    right hrightControl).1 hcandidate
                change I.toSOA.candidate
                  (left ++ Word.insertAt
                    (attachment.toIntervalWordAttachment.orderedAttachment
                      ).base second.yield
                    (attachment.toIntervalWordAttachment.orderedAttachment
                      ).rightSlot ++ right)
                rw [hbase, hrightSlot]
                rw [show
                  FactorTree.forestYield (first :: third :: rest) =
                    first.yield ++ FactorTree.forestYield (third :: rest) by
                    simp [FactorTree.forestYield]]
                rw [show
                  Word.insertAt
                      (first.yield ++
                        FactorTree.forestYield (third :: rest))
                      second.yield first.yield.length =
                    first.yield ++ second.yield ++
                      FactorTree.forestYield (third :: rest) by
                    simpa using
                      (Word.insertAt_left_decomposition
                        first.yield [] (FactorTree.forestYield
                          (third :: rest)) second.yield)]
                simpa [FactorTree.forestYield,
                  List.append_assoc] using hc
              · change
                  left ++ Word.insertAt
                      (attachment.toIntervalWordAttachment.orderedAttachment
                        ).base
                      second.yield
                      (attachment.toIntervalWordAttachment.orderedAttachment
                        ).rightSlot ++ right =
                    word
                rw [hbase, hrightSlot]
                rw [show
                  FactorTree.forestYield (first :: third :: rest) =
                    first.yield ++ FactorTree.forestYield (third :: rest) by
                    simp [FactorTree.forestYield]]
                rw [show
                  Word.insertAt
                      (first.yield ++
                        FactorTree.forestYield (third :: rest))
                      second.yield first.yield.length =
                    first.yield ++ second.yield ++
                      FactorTree.forestYield (third :: rest) by
                    simpa using
                      (Word.insertAt_left_decomposition
                        first.yield [] (FactorTree.forestYield
                          (third :: rest)) second.yield)]
                simpa [FactorTree.forestYield,
                  List.append_assoc] using hdecompose.symm
              · simpa [shorter, hdecompose] using hdelete
              · simpa [shorter, hdecompose] using hshort

theorem CandidateAlignedAttachedContraction.structural_or_mismatch
    [DecidableEq α]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (children : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    let ordered :=
      contraction.attachment.toIntervalWordAttachment.orderedAttachment
    (∃ emitter :
        ContextualStructuralEmitter α Wire C letter predicates.length
          Ctl Cut Macro,
      emitter.singletonChain.finalState ≠
        emitter.emitter.sourceState) ∨
      Word.insertAt ordered.base contraction.attachment.payload
          ordered.leftSlot ≠
        Word.insertAt ordered.base contraction.attachment.payload
          ordered.rightSlot := by
  dsimp only
  rcases contraction.attachment.completeCompilerResponse
      children predicates wireOf strongWire C letter
      control cut macroData with
    hstructural | hempty | hmismatch
  · exact Or.inl hstructural
  · exact False.elim (contraction.middle_ne_nil hempty)
  · exact Or.inr
      ((contraction.attachment.toIntervalWordAttachment.orderedAttachment
        ).mismatchHorn_derives_iff.mp hmismatch)

theorem CandidateAlignedAttachedContraction.rightInsertion_avoider
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word) :
    I.toSOA.Avoider
      (contraction.attachment.left ++
        Word.insertAt
          (contraction.attachment.toIntervalWordAttachment.orderedAttachment
            ).base
          contraction.attachment.payload
          (contraction.attachment.toIntervalWordAttachment.orderedAttachment
            ).rightSlot ++
        contraction.attachment.right) := by
  rw [contraction.rightInsertion_eq_word]
  exact hminimal.1

end NSSE
