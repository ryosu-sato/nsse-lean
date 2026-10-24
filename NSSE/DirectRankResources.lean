import NSSE.DirectRankTransition

/-! # Actual direct rank-step source invariants and computed resource bounds -/

namespace NSSE.DirectRankResources

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ArrayAtomExistentialPackages
open RankAvoidanceCompiler (Problem Fresh seed last liftedRows liftedCandidate)
open DirectRankTransition
open ComputedScalarLoweringBudget ExactReachabilitySize

universe u v w

theorem rowSize_parameter_map {L : FirstOrder.Language.{u,v}} {P : Type w} {P' : Type*}
    {n : Nat} (f : P → P') (R : Row L P n) :
    rowSize (RowParameterTransport.mapRow f R) = rowSize R := by
  simp only [rowSize, RowParameterTransport.mapRow, nodes_relabel]

theorem cleaned_qf (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate) :
    RowQF (cleaned I).2 :=
  DirectEmptyTailRemoval.subtractFamily_qf _ _ _
    (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
    (RankCleanedQuantifierFree.parameter_map_qf _ _ hc)

theorem next_rows_qf (I : Problem) (i : Fin (next I).rowCount) : RowQF ((next I).rows i) :=
  RankNextQuantifierFree.map_qf _ _ (RankNextQuantifierFree.outside_qf _ _)

theorem next_candidate_qf (I : Problem) : RowQF (next I).candidate :=
  RankNextQuantifierFree.candidate_qf _ _

theorem cleaned_next_qf (I : Problem) : RowQF (cleaned (next I)).2 :=
  cleaned_qf _ (next_rows_qf I) (next_candidate_qf I)

def cleanedStateCount (I : Problem) :=
  I.states * ((List.finRange I.rowCount).map (fun i => 2^(3*I.rowStates i)+1)).prod

def cleanedGuardBound (I : Problem) :=
  rowSize I.candidate + DirectEmptyTailSize.extra (EmptyTailRemoval.rowList I.rows)

theorem cleaned_states (I : Problem) : (cleaned I).1 = cleanedStateCount I :=
  DirectEmptyTailRemoval.subtractFamily_states _ _ _

theorem next_states (I : Problem) : (next I).states = cleanedStateCount I+1 := by
  dsimp only [next]
  rw [BlockCandidateTransport.length_states, cleaned_states]

theorem extra_parameter_map {L : FirstOrder.Language.{u,v}} {P : Type w} {P' : Type*}
    {k : Nat} {ns : Fin k → Nat} (f : P → P') (rows : (i : Fin k) → Row L P (ns i)) :
    DirectEmptyTailSize.extra (EmptyTailRemoval.rowList (fun i => RowParameterTransport.mapRow f (rows i))) =
      DirectEmptyTailSize.extra (EmptyTailRemoval.rowList rows) := by
  simp only [DirectEmptyTailSize.extra, EmptyTailRemoval.rowList, List.map_map,
    Function.comp_def, DirectEmptyTailSize.rowContribution, rowSize_parameter_map]

theorem cleaned_fields (I : Problem) : DirectRowBooleanSize.Fields (cleaned I).2 (cleanedGuardBound I) := by
  have h := DirectEmptyTailSize.subtractFamily_fields
    (fun i => RowParameterTransport.mapRow (Sum.inl : I.Parameters → Fresh I) (I.rows i))
    (liftedCandidate I) (last I)
  simpa only [liftedCandidate, liftedRows, rowSize_parameter_map, extra_parameter_map, cleanedGuardBound] using h

theorem cleaned_size (I : Problem) : rowSize (cleaned I).2 ≤
    DirectEmptyTailSize.totalBound (cleanedStateCount I) (cleanedGuardBound I) := by
  have h := cleaned_fields I
  have hh := RankNextGuardSize.rowSize_le _ h.toRowSize h.initial h.final
  simpa only [cleaned_states, DirectEmptyTailSize.totalBound] using hh

theorem next_row_size (I : Problem) (i : Fin (next I).rowCount) :
    let n := I.rowStates (UnifiedBlockPresentation.branchAt I.rowStates i).1
    rowSize ((next I).rows i) ≤ RankNextGuardSize.outsideSizeBound n := by
  dsimp only [next, UnifiedBlockPresentation.familyRows, UnifiedBlockPresentation.compileRow]
  rw [RankNextGuardSize.rowSize_map]
  exact RankNextGuardSize.outside_size _ _

theorem next_candidate_size (I : Problem) : rowSize (next I).candidate ≤
    RankNextGuardSize.candidateSizeBound (cleanedStateCount I) := by
  have h := RankNextGuardSize.candidate_size I.rowStates (cleaned I).1
  simpa only [cleaned_states] using h

end NSSE.DirectRankResources
