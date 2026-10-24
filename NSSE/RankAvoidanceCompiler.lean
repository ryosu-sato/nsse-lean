import NSSE.EmptyTailRemoval
import NSSE.RowParameterTransport

/-! # A complete syntactic rank-bounded avoidance compiler

The only recursion decreases the supplied natural-number rank. Every step
constructs fresh parameters, actual empty-tail subtraction, one common word
presentation and the whole new candidate/row family. No model or truth
oracle is an input to the compiler.
-/

namespace NSSE.RankAvoidanceCompiler

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedRowFiring

/-- Finite-state syntax; the base signature and free-name type may vary
between recursive calls. All generated word signatures are relational. -/
structure Problem where
  language : FirstOrder.Language.{0, 0}
  Parameters : Type
  states : Nat
  candidate : Row language Parameters states
  rowCount : Nat
  rowStates : Fin rowCount → Nat
  rows : (i : Fin rowCount) → Row language Parameters (rowStates i)

abbrev Fresh (I : Problem) := I.Parameters ⊕ Fin 2

def seed (I : Problem) : Fresh I := .inr 0
def last (I : Problem) : Fresh I := .inr 1

def liftedCandidate (I : Problem) : Row I.language (Fresh I) I.states :=
  RowParameterTransport.mapRow Sum.inl I.candidate

def liftedRows (I : Problem) (i : Fin I.rowCount) : Row I.language (Fresh I) (I.rowStates i) :=
  RowParameterTransport.mapRow Sum.inl (I.rows i)

def cleaned (I : Problem) : EmptyTailRemoval.Candidate I.language (Fresh I) :=
  EmptyTailRemoval.subtractFamily (liftedRows I) (liftedCandidate I) (last I)

def presentation (I : Problem) :=
  UnifiedBlockPresentation.presentation (liftedRows I) (cleaned I).2 (seed I) (last I)

def next (I : Problem) : Problem where
  language := UnifiedBlockPresentation.language I.rowStates (cleaned I).1
  Parameters := Empty
  states := (BlockCandidateTransport.states (cleaned I).1).length
  candidate := BlockCandidateTransport.compile I.rowStates (cleaned I).1
  rowCount := (UnifiedBlockPresentation.branches I.rowStates).length
  rowStates := UnifiedBlockPresentation.familyStates I.rowStates
  rows := UnifiedBlockPresentation.familyRows I.rowStates (cleaned I).1

def stepModel (I : Problem) {D : Type*} [I.language.Structure D] (p : Fresh I → D) :
    (next I).language.Structure (List D) :=
  UnifiedBlockPresentation.model (liftedRows I) (cleaned I).2 (seed I) (last I) p

def lowerStep (I : Problem) (φ : (next I).language.Sentence) : I.language.Formula I.Parameters :=
  SymbolicReachability.closeColumn (UniformWordLowering.lower (presentation I) φ)

/-- At rank zero, the same actual block candidate is used just for
nonemptiness. At a successor, recurse on its full avoidance problem. -/
def solve : (h : Nat) → (I : Problem) → I.language.Formula I.Parameters
  | 0, I => RowRegularOperations.seedOnlyFormula I.candidate ⊔
      lowerStep I (RowRegularOperations.nonemptyFormula (next I).candidate)
  | h + 1, I => RowRegularOperations.seedOnlyFormula I.candidate ⊔
      lowerStep I (solve h (next I))

def Avoid (I : Problem) {D : Type*} [I.language.Structure D] (p : I.Parameters → D) : Prop :=
  ∃ s : D, ∃ body : List D, (I.candidate.dataNFA p).Accepts (s :: body) ∧
    ∀ i, ¬ Fires (I.rows i) p s body

def RankBound (I : Problem) {D : Type*} [I.language.Structure D] [DecidableEq D]
    (p : I.Parameters → D) (h : Nat) : Prop :=
  ∀ s body, (I.candidate.dataNFA p).Accepts (s :: body) →
    TerminalBorderRank.suffixBorderRank body ≤ h

theorem avoid_iff_lists (I : Problem) {D : Type*} [I.language.Structure D]
    (p : I.Parameters → D) (d : D)
    (hne : ∀ xs, (I.candidate.dataNFA p).Accepts xs → xs ≠ []) :
    Avoid I p ↔ ∃ xs : List D, (I.candidate.dataNFA p).Accepts xs ∧
      ∀ i, ¬ Fires (I.rows i) p (xs.head?.getD d) xs.tail := by
  constructor
  · rintro ⟨s, body, hC, hR⟩
    exact ⟨s :: body, hC, hR⟩
  · rintro ⟨xs, hC, hR⟩
    cases xs with
    | nil => exact False.elim (hne [] hC rfl)
    | cons s body => exact ⟨s, body, hC, hR⟩

theorem next_nonempty (I : Problem) {D : Type*} [I.language.Structure D]
    (p : Fresh I → D) (bs : List (List D)) :
    letI := stepModel I p
    ((next I).candidate.dataNFA Empty.elim).Accepts bs → bs ≠ [] := by
  intro hC
  exact ((BlockCandidateTransport.compile_correct (liftedRows I) (cleaned I).2
    (seed I) (last I) p Empty.elim bs).mp hC).1

theorem slice_iff_next (I : Problem) {D : Type*} [I.language.Structure D]
    (p : I.Parameters → D) (s a : D) :
    (∃ w : List D, (I.candidate.dataNFA p).Accepts (s :: (w ++ [a])) ∧
      ∀ i, ¬ Fires (I.rows i) p s (w ++ [a])) ↔
      letI := stepModel I (Sum.elim p ![s,a])
      Avoid (next I) (D := List D) Empty.elim := by
  let p' : Fresh I → D := Sum.elim p ![s,a]
  have he := EmptyTailRemoval.exists_full_avoider_iff_block
    (liftedRows I) (liftedCandidate I) (seed I) (last I) p'
  letI := stepModel I p'
  rw [avoid_iff_lists (next I) Empty.elim ([] : List D) (next_nonempty I p')]
  convert he using 1
  simp only [liftedCandidate, liftedRows, RowParameterTransport.dataNFA_map,
    RowParameterTransport.fires_map, p', seed, last, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem next_rank_bound (I : Problem) {D : Type*} [I.language.Structure D] [DecidableEq D]
    (p : I.Parameters → D) (s a : D) (h : Nat) (hb : RankBound I p (h + 1)) :
    letI := stepModel I (Sum.elim p ![s,a])
    RankBound (next I) (D := List D) Empty.elim h := by
  let p' : Fresh I → D := Sum.elim p ![s,a]
  letI := stepModel I p'
  intro U body hC
  have he := EmptyTailRemoval.block_candidate_rank_bound
    (liftedRows I) (liftedCandidate I) (seed I) (last I) p' (h + 1) (by omega)
    (by
      intro w hw
      rw [liftedCandidate, RowParameterTransport.dataNFA_map] at hw
      exact hb (p' (seed I)) w hw)
    (U :: body) hC
  simpa using he

theorem slice_zero_iff_nonempty (I : Problem) {D : Type*} [I.language.Structure D]
    [DecidableEq D] (p : I.Parameters → D) (s a : D) (hb : RankBound I p 0) :
    (∃ w : List D, (I.candidate.dataNFA p).Accepts (s :: (w ++ [a])) ∧
      ∀ i, ¬ Fires (I.rows i) p s (w ++ [a])) ↔
      letI := stepModel I (Sum.elim p ![s,a])
      ∃ bs : List (List D), ((next I).candidate.dataNFA Empty.elim).Accepts bs := by
  let p' : Fresh I → D := Sum.elim p ![s,a]
  have he := EmptyTailRemoval.rank_zero_iff_block_nonempty
    (liftedRows I) (liftedCandidate I) (seed I) (last I) p'
    (by
      intro w hw
      rw [liftedCandidate, RowParameterTransport.dataNFA_map] at hw
      exact Nat.eq_zero_of_le_zero (hb (p' (seed I)) w hw))
  convert he using 1
  simp only [liftedCandidate, liftedRows, RowParameterTransport.dataNFA_map,
    RowParameterTransport.fires_map, p', seed, last, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Only the two fresh outer-sort values are bound here. All quantifiers
of the word-level sentence have already been handled by uniform lowering. -/
theorem lowerStep_correct (I : Problem) {D : Type*} [I.language.Structure D]
    (p : I.Parameters → D) (φ : (next I).language.Sentence) :
    (lowerStep I φ).Realize p ↔ ∃ s a : D,
      letI := stepModel I (Sum.elim p ![s,a])
      Formula.Realize φ (Empty.elim : Empty → List D) := by
  rw [lowerStep, SymbolicReachability.realize_closeColumn]
  have he (xs : Fin 2 → D) :
      (UniformWordLowering.lower (presentation I) φ).Realize (Sum.elim p xs) ↔
        letI := stepModel I (Sum.elim p xs)
        Formula.Realize φ (Empty.elim : Empty → List D) := by
    letI := stepModel I (Sum.elim p xs)
    have hl := UniformWordLowering.lower_reverse_correct (presentation I) (Sum.elim p xs) φ
    refine hl.trans ?_
    rw [Sentence.Realize]
    exact iff_of_eq (congrArg (Formula.Realize φ) (Subsingleton.elim _ _))
  constructor
  · rintro ⟨xs, hx⟩
    refine ⟨xs 0, xs 1, ?_⟩
    have hxs : ![xs 0, xs 1] = xs := by funext i; fin_cases i <;> rfl
    rw [hxs]
    exact (he xs).mp hx
  · rintro ⟨s, a, ha⟩
    exact ⟨![s,a], (he ![s,a]).mpr ha⟩

theorem avoid_split (I : Problem) {D : Type*} [I.language.Structure D] (p : I.Parameters → D) :
    Avoid I p ↔ (∃ s : D, (I.candidate.dataNFA p).Accepts [s]) ∨
      ∃ s a : D, ∃ w : List D, (I.candidate.dataNFA p).Accepts (s :: (w ++ [a])) ∧
        ∀ i, ¬ Fires (I.rows i) p s (w ++ [a]) := by
  constructor
  · rintro ⟨s, body, hC, hR⟩
    by_cases hn : body = []
    · subst body
      exact Or.inl ⟨s, hC⟩
    · refine Or.inr ⟨s, body.getLast hn, body.dropLast, ?_⟩
      simpa only [List.dropLast_concat_getLast hn] using And.intro hC hR
  · rintro (⟨s, hC⟩ | ⟨s, a, w, hC, hR⟩)
    · exact ⟨s, [], hC, fun i => not_fires_nil (I.rows i) p s⟩
    · exact ⟨s, w ++ [a], hC, hR⟩

universe u

/-- The complete uniform rank theorem, for the actual recursively computed
FO formula, arbitrary structures and one fixed original parameter valuation.
The whole-candidate rank promise is the ONLY mathematical premise. -/
theorem solve_correct (h : Nat) :
    ∀ (I : Problem) {D : Type u} [I.language.Structure D] [DecidableEq D]
      (p : I.Parameters → D), RankBound I p h →
        ((solve h I).Realize p ↔ Avoid I p) := by
  induction h with
  | zero =>
      intro I D M dec p hb
      rw [solve, Formula.realize_sup, RowRegularOperations.seedOnlyFormula_correct,
        lowerStep_correct, avoid_split]
      apply or_congr Iff.rfl
      apply exists_congr
      intro s
      apply exists_congr
      intro a
      letI := stepModel I (Sum.elim p ![s,a])
      rw [RowRegularOperations.nonemptyFormula_correct]
      exact (slice_zero_iff_nonempty I p s a hb).symm
  | succ h ih =>
      intro I D M dec p hb
      rw [solve, Formula.realize_sup, RowRegularOperations.seedOnlyFormula_correct,
        lowerStep_correct, avoid_split]
      apply or_congr Iff.rfl
      apply exists_congr
      intro s
      apply exists_congr
      intro a
      letI := stepModel I (Sum.elim p ![s,a])
      exact (ih (next I) (D := List D) Empty.elim (next_rank_bound I p s a h hb)).trans
        (slice_iff_next I p s a).symm

end NSSE.RankAvoidanceCompiler
