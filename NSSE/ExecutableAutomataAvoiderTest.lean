import NSSE.BoundedAvoiderAtom

/-!
# Exact executable avoider test for an automata-presented SOA

Final-state tests for the candidate and both automata of every row make
all cut witnesses executable.  Scanning the finitely many cut pairs gives
an exact Boolean `RootCov` test and hence an `ExactAvoiderTest`.
-/

namespace NSSE

universe u vc vl vr

structure AutomataSOAFinalTests
    (I : AutomataSOAInstance α QC QL QR) where
  candidate : DFAFinalTest I.candidate
  left : ∀ row : DFA α QL × DFA α QR, DFAFinalTest row.1
  right : ∀ row : DFA α QL × DFA α QR, DFAFinalTest row.2

def rowCoversTest
    [DecidableEq α]
    {I : AutomataSOAInstance α QC QL QR}
    (tests : AutomataSOAFinalTests I)
    (row : DFA α QL × DFA α QR)
    (word : Word α) : Bool :=
  (List.range word.length).any fun j =>
    (List.range word.length).any fun t =>
      decide (j < t) &&
      (tests.left row).test (row.1.run (word.take j)) &&
      (tests.right row).test
        (row.2.run (Word.factor word j (t - j))) &&
      decide
        (Word.factor word j (word.length - t) =
          Word.factor word t (word.length - t))

theorem rowCoversTest_correct
    [DecidableEq α]
    {I : AutomataSOAInstance α QC QL QR}
    (tests : AutomataSOAFinalTests I)
    (row : DFA α QL × DFA α QR)
    (word : Word α) :
    rowCoversTest tests row word = true ↔
      SOAInstance.RowCovers
        (CapComponent.ofDFA row.1 row.2) word := by
  rw [SOAInstance.rowCovers_iff_cuts]
  constructor
  · intro htest
    simp only [rowCoversTest, List.any_eq_true] at htest
    obtain ⟨j, hjRange, t, htRange, hcuts⟩ := htest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcuts
    exact ⟨j, t, hcuts.1.1.1, List.mem_range.mp htRange,
      ((tests.left row).correct _).1 hcuts.1.1.2,
      ((tests.right row).correct _).1 hcuts.1.2,
      hcuts.2⟩
  · rintro ⟨j, t, hjt, ht, hleft, hright, hoccurs⟩
    simp only [rowCoversTest, List.any_eq_true]
    refine ⟨j, List.mem_range.mpr (Nat.lt_trans hjt ht),
      t, List.mem_range.mpr ht, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hjt, ((tests.left row).correct _).2 hleft⟩,
      ((tests.right row).correct _).2 hright⟩, hoccurs⟩

def rootCovTest
    [DecidableEq α]
    {I : AutomataSOAInstance α QC QL QR}
    (tests : AutomataSOAFinalTests I)
    (word : Word α) : Bool :=
  I.rows.any fun row => rowCoversTest tests row word

theorem rootCovTest_correct
    [DecidableEq α]
    {I : AutomataSOAInstance α QC QL QR}
    (tests : AutomataSOAFinalTests I)
    (word : Word α) :
    rootCovTest tests word = true ↔ I.toSOA.RootCov word := by
  unfold rootCovTest SOAInstance.RootCov
  rw [List.any_eq_true]
  constructor
  · rintro ⟨row, hrow, htest⟩
    exact ⟨CapComponent.ofDFA row.1 row.2,
      by
        simp only [AutomataSOAInstance.toSOA, List.mem_map]
        exact ⟨row, hrow, rfl⟩,
      (rowCoversTest_correct tests row word).1 htest⟩
  · rintro ⟨component, hcomponent, hcovers⟩
    simp only [AutomataSOAInstance.toSOA, List.mem_map] at hcomponent
    obtain ⟨row, hrow, rfl⟩ := hcomponent
    exact ⟨row, hrow,
      (rowCoversTest_correct tests row word).2 hcovers⟩

def automataAvoiderTest
    [DecidableEq α]
    {I : AutomataSOAInstance α QC QL QR}
    (tests : AutomataSOAFinalTests I) :
    ExactAvoiderTest I.toSOA where
  test := fun word =>
    tests.candidate.test (I.candidate.run word) &&
      !(rootCovTest tests word)
  correct := by
    intro word
    rw [Bool.and_eq_true]
    rw [Bool.not_eq_true']
    change
      (tests.candidate.test (I.candidate.run word) = true ∧
        rootCovTest tests word = false) ↔
      I.toSOA.candidate word ∧ ¬ I.toSOA.RootCov word
    constructor
    · rintro ⟨hcandidate, hrootFalse⟩
      refine ⟨(tests.candidate.correct _).1 hcandidate, ?_⟩
      intro hroot
      have hrootTrue := (rootCovTest_correct tests word).2 hroot
      rw [hrootFalse] at hrootTrue
      contradiction
    · rintro ⟨hcandidate, hnotRoot⟩
      refine ⟨(tests.candidate.correct _).2 hcandidate, ?_⟩
      cases htest : rootCovTest tests word with
      | false => rfl
      | true =>
          exact False.elim
            (hnotRoot ((rootCovTest_correct tests word).1 htest))

end NSSE
