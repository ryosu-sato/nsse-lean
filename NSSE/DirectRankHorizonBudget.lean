import NSSE.DirectRankHorizonStates

/-! # Closed presentation budgets from initial syntax and a numeric horizon -/

namespace NSSE.DirectRankHorizonBudget

open FirstOrder FirstOrder.Language
open RankAvoidanceCompiler (Problem liftedRows)
open DirectRankTransition DirectRankResources DirectRankStateRecurrence DirectRankHorizonStates
open ComputedScalarLoweringBudget DirectRankFormulaRecurrence

def rowTable (I : Problem) (H : Nat) := max (initialBudget I) (RankNextGuardSize.outsideSizeBound (rowLimit I H))
def candidateTable (I : Problem) (H : Nat) := max (initialBudget I) (RankNextGuardSize.candidateSizeBound (candidateBound I H))
def contribution (n B : Nat) := 5+DirectRowBooleanSize.complementBound (3*n) (DirectEmptyTailSize.emptyBound n B)
def guardBudget (I : Problem) (H : Nat) := candidateTable I H + rowCountBound I H*contribution (rowLimit I H) (rowTable I H)
def cleanedTable (I : Problem) (H : Nat) := DirectEmptyTailSize.totalBound (candidateBound I H) (guardBudget I H)
def presentationTable (I : Problem) (H : Nat) := rowCountBound I H+cleanedTable I H+rowCountBound I H*rowTable I H
def budget (I : Problem) (H : Nat) := max (candidateTable I H) (presentationTable I H)

theorem outside_mono {n m : Nat} (h : n ≤ m) :
    RankNextGuardSize.outsideSizeBound n ≤ RankNextGuardSize.outsideSizeBound m := by
  unfold RankNextGuardSize.outsideSizeBound; gcongr

theorem candidate_mono {n m : Nat} (h : n ≤ m) :
    RankNextGuardSize.candidateSizeBound n ≤ RankNextGuardSize.candidateSizeBound m := by
  unfold RankNextGuardSize.candidateSizeBound; gcongr

theorem contribution_mono {n m B C : Nat} (hn : n ≤ m) (hb : B ≤ C) : contribution n B ≤ contribution m C := by
  unfold contribution DirectRowBooleanSize.complementBound DirectRowBooleanSize.predecessorBound DirectEmptyTailSize.emptyBound
  gcongr

theorem row_table (I : Problem) (H t : Nat) (ht : t ≤ H) (i : Fin (descend t I).rowCount) :
    rowSize ((descend t I).rows i) ≤ rowTable I H := by
  cases t with
  | zero =>
    have hh := summand_le (fun j => rowSize (I.rows j)) i
    apply Nat.le_trans (m := initialBudget I) ?_ (le_max_left _ _)
    unfold initialBudget presentationSize
    change rowSize (I.rows i) ≤ _
    omega
  | succ t =>
    have hh := next_row_size (descend t I) i
    have hn := row_states I H t (by omega) (UnifiedBlockPresentation.branchAt (descend t I).rowStates i).1
    exact hh.trans ((outside_mono (by omega)).trans (le_max_right _ _))

theorem candidate_table (I : Problem) (H t : Nat) (ht : t ≤ H) :
    rowSize (descend t I).candidate ≤ candidateTable I H := by
  cases t with
  | zero =>
    apply Nat.le_trans (m := initialBudget I) ?_ (le_max_left _ _)
    unfold initialBudget presentationSize
    change rowSize I.candidate ≤ _
    omega
  | succ t =>
    have hh := next_candidate_size (descend t I)
    have hn := candidate_states I H (t+1) ht
    change (next (descend t I)).states+1 ≤ _ at hn
    rw [next_states] at hn
    exact hh.trans ((candidate_mono (by omega)).trans (le_max_right _ _))

theorem cleaned_guard (I : Problem) (H t : Nat) (ht : t ≤ H) :
    cleanedGuardBound (descend t I) ≤ guardBudget I H := by
  have hr (i : Fin (descend t I).rowCount) : contribution ((descend t I).rowStates i)
      (rowSize ((descend t I).rows i)) ≤ contribution (rowLimit I H) (rowTable I H) :=
    contribution_mono (Nat.le_trans (Nat.le_succ _) (row_states I H t ht i)) (row_table I H t ht i)
  have hs := sum_map_le (List.finRange (descend t I).rowCount)
    (fun i => contribution ((descend t I).rowStates i) (rowSize ((descend t I).rows i)))
    (contribution (rowLimit I H) (rowTable I H)) (fun i _ => hr i)
  simp only [List.length_finRange] at hs
  have hc := candidate_table I H t ht
  have hk := Nat.mul_le_mul_right (contribution (rowLimit I H) (rowTable I H)) (row_count I H t ht)
  unfold cleanedGuardBound DirectEmptyTailSize.extra EmptyTailRemoval.rowList
  simp only [List.map_map, Function.comp_def, DirectEmptyTailSize.rowContribution]
  change rowSize (descend t I).candidate +
    ((List.finRange (descend t I).rowCount).map (fun i => contribution ((descend t I).rowStates i)
      (rowSize ((descend t I).rows i)))).sum ≤ _
  unfold guardBudget
  omega

theorem cleaned_table (I : Problem) (H t : Nat) (ht : t+1 ≤ H) :
    rowSize (cleaned (descend t I)).2 ≤ cleanedTable I H := by
  have hg := cleaned_guard I H t (by omega)
  have hn := candidate_states I H (t+1) ht
  change (next (descend t I)).states+1 ≤ _ at hn
  rw [next_states] at hn
  apply (cleaned_size (descend t I)).trans
  unfold cleanedTable DirectEmptyTailSize.totalBound
  gcongr <;> omega

theorem presentation_table (I : Problem) (H t : Nat) (ht : t+1 ≤ H) :
    presentationBudget (descend t I) ≤ presentationTable I H := by
  have hc := cleaned_table I H t ht
  have hk := row_count I H t (by omega)
  have hr (i : Fin (descend t I).rowCount) : rowSize (liftedRows (descend t I) i) ≤ rowTable I H := by
    rw [RankAvoidanceCompiler.liftedRows, rowSize_parameter_map]
    exact row_table I H t (by omega) i
  have hs : (∑ i, rowSize (liftedRows (descend t I) i)) ≤ (descend t I).rowCount*rowTable I H := by
    calc
      _ ≤ ∑ _i : Fin (descend t I).rowCount, rowTable I H := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp
  have hm := Nat.mul_le_mul_right (rowTable I H) hk
  unfold presentationBudget presentationSize presentationTable
  omega

theorem common_bound_at (I : Problem) (H h t : Nat) (ht : t+h+1 ≤ H) :
    commonBudget h (descend t I) ≤ budget I H := by
  induction h generalizing t with
  | zero =>
    apply max_le
    · apply max_le
      · exact (candidate_table I H t (by omega)).trans (le_max_left _ _)
      · exact (presentation_table I H t (by omega)).trans (le_max_right _ _)
    · exact (candidate_table I H (t+1) (by omega)).trans (le_max_left _ _)
  | succ h ih =>
    apply max_le
    · apply max_le
      · exact (candidate_table I H t (by omega)).trans (le_max_left _ _)
      · exact (presentation_table I H t (by omega)).trans (le_max_right _ _)
    · exact ih (t+1) (by omega)

theorem common_bound (I : Problem) (h : Nat) : commonBudget h I ≤ budget I (h+1) :=
  common_bound_at I (h+1) h 0 (by omega)

theorem solve_bound_initial (h : Nat) (I : Problem) (hr : ∀ i, ArrayAtomExistentialPackages.RowQF (I.rows i))
    (hc : ArrayAtomExistentialPackages.RowQF I.candidate) :
    ExactReachabilitySize.nodes (DirectExistentialRankCompiler.solve h I hr hc).toFormula+1 ≤
      (DirectRankFormulaClosedBound.base (budget I (h+1)))^(4^(h+1)) :=
  (DirectRankFormulaRecurrence.solve_bound h I hr hc _ (common_bound I h)).trans
    (DirectRankFormulaClosedBound.majorant_closed _ h)

end NSSE.DirectRankHorizonBudget
