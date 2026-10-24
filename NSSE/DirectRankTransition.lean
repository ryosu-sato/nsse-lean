import NSSE.DirectEmptyTailGeometry

/-! # Actual direct-cleanup rank transition, with semantic rank descent -/

namespace NSSE.DirectRankTransition

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedRowFiring
open RankAvoidanceCompiler (Problem Fresh seed last liftedCandidate liftedRows Avoid RankBound avoid_iff_lists)

def cleaned (I : Problem) : EmptyTailRemoval.Candidate I.language (Fresh I) :=
  DirectEmptyTailRemoval.subtractFamily (liftedRows I) (liftedCandidate I) (last I)

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
  have he := DirectEmptyTailGeometry.exists_full_avoider_iff_block
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
  have he := DirectEmptyTailGeometry.block_candidate_rank_bound
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
  have he := DirectEmptyTailGeometry.rank_zero_iff_block_nonempty
    (liftedRows I) (liftedCandidate I) (seed I) (last I) p'
    (by
      intro w hw
      rw [liftedCandidate, RowParameterTransport.dataNFA_map] at hw
      exact Nat.eq_zero_of_le_zero (hb (p' (seed I)) w hw))
  convert he using 1
  simp only [liftedCandidate, liftedRows, RowParameterTransport.dataNFA_map,
    RowParameterTransport.fires_map, p', seed, last, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]


end NSSE.DirectRankTransition
