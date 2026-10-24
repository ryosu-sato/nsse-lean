import NSSE.DirectRankResources

/-! # Exact state recurrences of the actual optimized rank transition -/

namespace NSSE.DirectRankStateRecurrence

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks
open RankAvoidanceCompiler (Problem)
open DirectRankTransition DirectRankResources

theorem endpoints_length (n : Nat) : (UnifiedBlockPresentation.endpoints n).length = n^4 := by
  simp [UnifiedBlockPresentation.endpoints, List.length_flatMap]
  ring

theorem branches_length {k : Nat} (ns : Fin k → Nat) :
    (UnifiedBlockPresentation.branches ns).length = ((List.finRange k).map (fun i => 2*(ns i)^4)).sum := by
  simp only [UnifiedBlockPresentation.branches, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [List.length_flatMap, endpoints_length, Nat.mul_comm]

theorem next_rowCount (I : Problem) :
    (next I).rowCount = ((List.finRange I.rowCount).map (fun i => 2*(I.rowStates i)^4)).sum :=
  branches_length _

theorem next_rowStates (I : Problem) (i : Fin (next I).rowCount) :
    (next I).rowStates i = 4*I.rowStates (UnifiedBlockPresentation.branchAt I.rowStates i).1+2 :=
  SymbolicOutsideController.length_states _

def descend : Nat → Problem → Problem
  | 0, I => I
  | h+1, I => next (descend h I)

theorem descendant_rows_qf (h : Nat) (I : Problem) :
    ∀ i, ArrayAtomExistentialPackages.RowQF ((descend (h+1) I).rows i) := next_rows_qf _

theorem descendant_candidate_qf (h : Nat) (I : Problem) :
    ArrayAtomExistentialPackages.RowQF (descend (h+1) I).candidate := next_candidate_qf _

theorem descendant_row_states (I : Problem) (b : Nat) (hb : ∀ i, I.rowStates i+1 ≤ b) (h : Nat) :
    ∀ i, (descend h I).rowStates i+1 ≤ b*4^h := by
  induction h with
  | zero => simpa [descend] using hb
  | succ h ih =>
    intro i
    change (next (descend h I)).rowStates i+1 ≤ _
    rw [next_rowStates, Nat.pow_succ]
    have hi := ih (UnifiedBlockPresentation.branchAt (descend h I).rowStates i).1
    calc
      _ ≤ 4*((descend h I).rowStates (UnifiedBlockPresentation.branchAt (descend h I).rowStates i).1+1) := by omega
      _ ≤ 4*(b*4^h) := Nat.mul_le_mul_left 4 hi
      _ = _ := by ring

end NSSE.DirectRankStateRecurrence
