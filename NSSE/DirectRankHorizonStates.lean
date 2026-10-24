import NSSE.DirectRankFormulaClosedBound

/-! # Closed horizon-wide state bounds from actual initial input syntax -/

namespace NSSE.DirectRankHorizonStates

open FirstOrder FirstOrder.Language
open RankAvoidanceCompiler (Problem)
open DirectRankTransition DirectRankResources DirectRankStateRecurrence ComputedScalarLoweringBudget

def initialBudget (I : Problem) := presentationSize I.rows I.candidate+1
def rowLimit (I : Problem) (H : Nat) := initialBudget I*4^H
def rowFactor (I : Problem) (H : Nat) := 2*(rowLimit I H)^4+1
def rowCountBound (I : Problem) (H : Nat) := initialBudget I*(rowFactor I H)^H
def stepExponent (I : Problem) (H : Nat) := rowCountBound I H*(3*rowLimit I H+1)+1
def candidateBound (I : Problem) (H : Nat) := initialBudget I*2^(H*stepExponent I H)

theorem initial_rows (I : Problem) (i : Fin I.rowCount) : I.rowStates i+1 ≤ initialBudget I := by
  have := (rows_budget I.rows I.candidate i).states
  unfold initialBudget; omega

theorem initial_count (I : Problem) : I.rowCount ≤ initialBudget I := by
  have := row_count_le I.rows I.candidate
  unfold initialBudget; omega

theorem initial_candidate (I : Problem) : I.states+1 ≤ initialBudget I := by
  have := (candidate_budget I.rows I.candidate).states
  unfold initialBudget; omega

theorem row_states (I : Problem) (H t : Nat) (ht : t ≤ H) (i : Fin (descend t I).rowCount) :
    (descend t I).rowStates i+1 ≤ rowLimit I H := by
  exact (descendant_row_states I (initialBudget I) (initial_rows I) t i).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) ht))

theorem sum_map_le {α : Type*} (as : List α) (f : α → Nat) (B : Nat) (h : ∀ a ∈ as, f a ≤ B) :
    (as.map f).sum ≤ as.length*B := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have hh := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem prod_map_le {α : Type*} (as : List α) (f : α → Nat) (B : Nat) (h : ∀ a ∈ as, f a ≤ B) :
    (as.map f).prod ≤ B^as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ht := ih (fun b hb => h b (by simp [hb]))
    simpa only [List.map_cons, List.prod_cons, List.length_cons, pow_succ'] using Nat.mul_le_mul (h a (by simp)) ht

theorem next_count_le (I : Problem) (Q : Nat) (hq : ∀ i, I.rowStates i ≤ Q) :
    (next I).rowCount ≤ I.rowCount*(2*Q^4+1) := by
  rw [next_rowCount]
  have hh := sum_map_le (List.finRange I.rowCount) (fun i => 2*(I.rowStates i)^4) (2*Q^4+1) (by
    intro i _
    exact (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hq i) 4)).trans (by omega))
  simpa only [List.length_finRange] using hh

theorem row_count_at (I : Problem) (H t : Nat) (ht : t ≤ H) :
    (descend t I).rowCount ≤ initialBudget I*(rowFactor I H)^t := by
  induction t with
  | zero => simpa only [descend, pow_zero, Nat.mul_one] using initial_count I
  | succ t ih =>
    have hi := ih (by omega)
    have hnext := next_count_le (descend t I) (rowLimit I H) (fun i =>
      Nat.le_trans (Nat.le_succ _) (row_states I H t (by omega) i))
    change (next (descend t I)).rowCount ≤ _
    calc
      _ ≤ (descend t I).rowCount*rowFactor I H := hnext
      _ ≤ (initialBudget I*(rowFactor I H)^t)*rowFactor I H := Nat.mul_le_mul_right _ hi
      _ = _ := by rw [pow_succ, Nat.mul_assoc]

theorem row_count (I : Problem) (H t : Nat) (ht : t ≤ H) :
    (descend t I).rowCount ≤ rowCountBound I H := by
  apply (row_count_at I H t ht).trans
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by unfold rowFactor; omega) ht

theorem factor_le (n Q : Nat) (hn : n ≤ Q) : 2^(3*n)+1 ≤ 2^(3*Q+1) := by
  have h₁ : 1 ≤ 2^(3*Q) := Nat.one_le_pow _ _ (by decide)
  have h₂ : 2^(3*n) ≤ 2^(3*Q) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

theorem next_candidate_le (I : Problem) (Q K : Nat) (hq : ∀ i, I.rowStates i ≤ Q) (hk : I.rowCount ≤ K) :
    (next I).states+1 ≤ (I.states+1)*2^(K*(3*Q+1)+1) := by
  have hp := prod_map_le (List.finRange I.rowCount) (fun i => 2^(3*I.rowStates i)+1) (2^(3*Q+1))
    (fun i _ => factor_le _ _ (hq i))
  simp only [List.length_finRange, ← pow_mul] at hp
  have he : (3*Q+1)*I.rowCount ≤ K*(3*Q+1) := by nlinarith
  have hp' := hp.trans (Nat.pow_le_pow_right (by decide) he)
  have h₁ : 1 ≤ 2^(K*(3*Q+1)) := Nat.one_le_pow _ _ (by decide)
  rw [next_states]
  unfold cleanedStateCount
  rw [pow_succ]
  nlinarith

theorem candidate_at (I : Problem) (H t : Nat) (ht : t ≤ H) :
    (descend t I).states+1 ≤ initialBudget I*2^(t*stepExponent I H) := by
  induction t with
  | zero => simpa only [descend, Nat.zero_mul, pow_zero, Nat.mul_one] using initial_candidate I
  | succ t ih =>
    have hi := ih (by omega)
    have hn := next_candidate_le (descend t I) (rowLimit I H) (rowCountBound I H)
      (fun i => Nat.le_trans (Nat.le_succ _) (row_states I H t (by omega) i))
      (row_count I H t (by omega))
    change (next (descend t I)).states+1 ≤ _
    calc
      _ ≤ ((descend t I).states+1)*2^stepExponent I H := hn
      _ ≤ (initialBudget I*2^(t*stepExponent I H))*2^stepExponent I H := Nat.mul_le_mul_right _ hi
      _ = _ := by rw [Nat.mul_assoc, ← pow_add]; congr 2; ring

theorem candidate_states (I : Problem) (H t : Nat) (ht : t ≤ H) :
    (descend t I).states+1 ≤ candidateBound I H := by
  apply (candidate_at I H t ht).trans
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ht)

end NSSE.DirectRankHorizonStates
