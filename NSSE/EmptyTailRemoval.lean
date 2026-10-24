import NSSE.EmptyTailFiring

/-! # Actual finite removal of every empty-tail firing, uniformly at any rank level -/

namespace NSSE.EmptyTailRemoval

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedRowFiring

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

abbrev Candidate (L : FirstOrder.Language.{u, v}) (P : Type w) := (n : Nat) × Row L P n

def subtractList (C : Candidate L P) (rows : List (Candidate L P)) (last : P) : Candidate L P :=
  match rows with
  | [] => C
  | R :: rows => subtractList
      ⟨_, RowRegularOperations.difference C.2 (EmptyTailFiring.compile R.2 last)⟩ rows last

theorem subtractList_correct (C : Candidate L P) (rows : List (Candidate L P)) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((subtractList C rows last).2.dataNFA p).Accepts xs ↔
      (C.2.dataNFA p).Accepts xs ∧ ∀ R ∈ rows, ¬ EmptyTailFiring.Witness R.2 last p xs := by
  induction rows generalizing C with
  | nil => simp [subtractList]
  | cons R rows ih =>
      rw [subtractList, ih, RowRegularOperations.difference_correct, EmptyTailFiring.compile_witness]
      simp only [List.forall_mem_cons]
      tauto

def rowList (rows : (i : Fin k) → Row L P (ns i)) : List (Candidate L P) :=
  (List.finRange k).map fun i => ⟨ns i, rows i⟩

def subtractFamily (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P) : Candidate L P :=
  subtractList ⟨c, C⟩ (rowList rows) last

theorem subtractFamily_all_inputs (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((subtractFamily rows C last).2.dataNFA p).Accepts xs ↔
      (C.dataNFA p).Accepts xs ∧ ∀ i, ¬ EmptyTailFiring.Witness (rows i) last p xs := by
  rw [subtractFamily, subtractList_correct]
  simp [rowList]

/-- On the actual terminal slice, this is exactly C minus the union of all
old empty-tail firing languages, including nondeterministic marked controls. -/
theorem subtractFamily_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (seed : D) (w : List D) :
    ((subtractFamily rows C last).2.dataNFA p).Accepts (seed :: (w ++ [p last])) ↔
      (C.dataNFA p).Accepts (seed :: (w ++ [p last])) ∧
        ∀ i, ¬ EmptyTailFires (rows i) p seed (w ++ [p last]) := by
  rw [subtractFamily_all_inputs]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  rw [EmptyTailFiring.witness_iff_emptyTail]
  exact lastOr_append_singleton seed (p last) (seed :: w)

/-- All other candidate constraints, including the old rank promise, are
retained on EVERY input; only acceptance is removed, never added. -/
theorem subtractFamily_subset (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((subtractFamily rows C last).2.dataNFA p).Accepts xs → (C.dataNFA p).Accepts xs :=
  fun h => ((subtractFamily_all_inputs rows C last p xs).mp h).1

theorem subtractFamily_avoidance (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (seed : D) (w : List D) :
    (((subtractFamily rows C last).2.dataNFA p).Accepts (seed :: (w ++ [p last])) ∧
      ∀ i, ¬ PositiveFires (rows i) p seed (w ++ [p last])) ↔
    ((C.dataNFA p).Accepts (seed :: (w ++ [p last])) ∧
      ∀ i, ¬ Fires (rows i) p seed (w ++ [p last])) := by
  rw [subtractFamily_correct]
  simp only [fires_iff_positive_or_empty, not_or, forall_and]
  tauto

/-- Full candidate avoidance, with the actual empty-tail subtraction
constructed INSIDE the step, not an external no-empty-firing hypothesis. -/
theorem exists_full_avoider_iff_block (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P → D) :
    (∃ w : List D, (C.dataNFA p).Accepts (p seed :: (w ++ [p last])) ∧
      ∀ i, ¬ Fires (rows i) p (p seed) (w ++ [p last])) ↔
      let C0 := subtractFamily rows C last
      letI := UnifiedBlockPresentation.model rows C0.2 seed last p
      ∃ bs : List (List D),
        ((BlockCandidateTransport.compile ns C0.1).dataNFA (Empty.elim : Empty → List D)).Accepts bs ∧
        ∀ i : Fin (UnifiedBlockPresentation.branches ns).length,
          ¬ Fires (UnifiedBlockPresentation.familyRows ns C0.1 i) (Empty.elim : Empty → List D)
            (bs.head?.getD []) bs.tail := by
  let C0 := subtractFamily rows C last
  have h := BlockCandidateTransport.exists_avoider_iff rows C0.2 seed last p
  refine Iff.trans ?_ h
  apply exists_congr
  intro w
  exact (subtractFamily_avoidance rows C last p (p seed) w).symm

/-- The complete preprocessed candidate keeps the original rank promise,
so the actual recursive input has the lower rank on ALL its accepted words. -/
theorem block_candidate_rank_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] [DecidableEq D] (p : P → D) (h : Nat) (hh : 0 < h)
    (hbound : ∀ w, (C.dataNFA p).Accepts (p seed :: w) → TerminalBorderRank.suffixBorderRank w ≤ h)
    (bs : List (List D)) :
    let C0 := subtractFamily rows C last
    letI := UnifiedBlockPresentation.model rows C0.2 seed last p
    ((BlockCandidateTransport.compile ns C0.1).dataNFA (Empty.elim : Empty → List D)).Accepts bs →
      TerminalBorderRank.suffixBorderRank bs.tail ≤ h - 1 := by
  apply BlockCandidateTransport.candidate_rank_bound rows (subtractFamily rows C last).2 seed last p h hh
  intro w hw
  exact hbound w (subtractFamily_subset rows C last p (p seed :: w) hw)

theorem no_positive_of_rank_zero (R : Row L P c) {D : Type*} [L.Structure D] [DecidableEq D]
    (p : P → D) (seed : D) (body : List D) (hzero : TerminalBorderRank.suffixBorderRank body = 0) :
    ¬ PositiveFires R p seed body := by
  rintro ⟨j, t, hfire, ht⟩
  exact TerminalBorderRank.rank_zero_no_occursSuffixAt body hzero j t hfire.1 ht hfire.2.2.2.2

/-- At rank zero, the SAME actual block candidate can be used just for
nonemptiness. No recursive call at a negative rank or assumed slice NFA. -/
theorem rank_zero_iff_block_nonempty (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] [DecidableEq D] (p : P → D)
    (hbound : ∀ w, (C.dataNFA p).Accepts (p seed :: w) → TerminalBorderRank.suffixBorderRank w = 0) :
    (∃ w : List D, (C.dataNFA p).Accepts (p seed :: (w ++ [p last])) ∧
      ∀ i, ¬ Fires (rows i) p (p seed) (w ++ [p last])) ↔
      let C0 := subtractFamily rows C last
      letI := UnifiedBlockPresentation.model rows C0.2 seed last p
      ∃ bs : List (List D),
        ((BlockCandidateTransport.compile ns C0.1).dataNFA (Empty.elim : Empty → List D)).Accepts bs := by
  let C0 := subtractFamily rows C last
  constructor
  · intro h
    obtain ⟨bs, hC, _⟩ := (exists_full_avoider_iff_block rows C seed last p).mp h
    exact ⟨bs, hC⟩
  · rintro ⟨bs, hC⟩
    obtain ⟨hne, _, hC0⟩ :=
      (BlockCandidateTransport.compile_correct rows C0.2 seed last p Empty.elim bs).mp hC
    obtain ⟨w, hw⟩ := BlockCandidateTransport.decode_terminal (p last) bs hne
    rw [hw] at hC0
    have hCold := subtractFamily_subset rows C last p (p seed :: (w ++ [p last])) hC0
    refine ⟨w, (subtractFamily_avoidance rows C last p (p seed) w).mp ⟨hC0, ?_⟩⟩
    intro i
    exact no_positive_of_rank_zero (rows i) p (p seed) (w ++ [p last]) (hbound _ hCold)

end NSSE.EmptyTailRemoval
