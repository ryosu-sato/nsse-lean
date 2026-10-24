import NSSE.StoredNextCandidateStates
import NSSE.RankNextQuantifierFree

/-! Actual next-candidate labels in the common next-rank relation language. -/
namespace NSSE.StoredNextCandidateGuards
open FirstOrder FirstOrder.Language StoredRelationalFormula
variable {k c : Nat} (ns : Fin k → Nat)

def noA : Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0 :=
  .rel .noA ⟨[.inl (.inr 0)],rfl⟩
def block (q r : Fin c) : Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0 :=
  .rel (.candidate (.block q r)) ⟨[.inl (.inr 0)],rfl⟩
def firstTerm (r q : Fin c) : Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0 × Nat :=
  (StoredArrayEquality.conj (.rel (.candidate (.initial q)) ⟨[],rfl⟩) (block ns q r),19)

theorem noA_value : denote (noA (c := c) ns) = BlockCandidateTransport.noAAtom ns c := by
  change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext i; fin_cases i; rfl
theorem block_value (q r : Fin c) : denote (block ns q r) =
    (UnifiedBlockPresentation.candidateHom ns c).onFormula (SymbolicOutsideController.blockAtom q r) := by
  change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext i; fin_cases i; rfl
theorem firstTerm_value (r q : Fin c) : denote (firstTerm ns r q).1 =
    ((UnifiedBlockPresentation.candidateHom ns c).onFormula (SymbolicOutsideController.initialAtom q)).relabel Sum.inl ⊓
    (UnifiedBlockPresentation.candidateHom ns c).onFormula (SymbolicOutsideController.blockAtom q r) := by
  have hi : denote (.rel (.candidate (.initial q)) ⟨[],rfl⟩ : Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0) =
      ((UnifiedBlockPresentation.candidateHom ns c).onFormula (SymbolicOutsideController.initialAtom q)).relabel Sum.inl := by
    change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
    congr 1
    funext i; exact i.elim0
  change denote (.rel (.candidate (.initial q)) ⟨[],rfl⟩ : Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0) ⊓
    denote (block ns q r) = _
  rw [hi,block_value]

def initial : Option (Fin c) → Data (UnifiedBlockPresentation.Rel ns c) Empty 0 × Nat
  | none => (.imp .falsum .falsum,3)
  | some _ => (.falsum,2)
def final : Option (Fin c) → Data (UnifiedBlockPresentation.Rel ns c) Empty 0 × Nat
  | none => (.falsum,2)
  | some q => (.rel (.candidate (.final q)) ⟨[],rfl⟩,4)
def data : Option (Fin c) → Option (Fin c) → Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0 × Nat
  | _,none => (.falsum,2)
  | none,some r =>
    let a := StoredRunTable.any c (firstTerm ns r)
    (StoredArrayEquality.conj (noA ns) a.1,13+a.2)
  | some q,some r => (StoredArrayEquality.conj (noA ns) (block ns q r),19)

theorem initial_value (q : Option (Fin c)) : denote (initial ns q).1 = BlockCandidateTransport.initialGuard ns c q := by
  cases q <;> rfl
theorem final_value (q : Option (Fin c)) : denote (final ns q).1 = BlockCandidateTransport.finalGuard ns c q := by
  cases q with
  | none => rfl
  | some q =>
    change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
    congr 1
    funext i; exact i.elim0
theorem data_value (q r : Option (Fin c)) : denote (data ns q r).1 = BlockCandidateTransport.dataGuard ns c q r := by
  cases q <;> cases r <;> simp only [data,StoredArrayEquality.conj,denote,StoredRunTable.any_value,
    noA_value,firstTerm_value,block_value,BlockCandidateTransport.dataGuard]; all_goals rfl

def budget (c : Nat) := 20+StoredRunTable.anyBudget c 19
def sizeBudget (c : Nat) := 7+10*c

theorem initial_bound (q : Option (Fin c)) : (initial ns q).2 ≤ budget c := by
  cases q <;> simp only [initial,budget] <;> omega
theorem final_bound (q : Option (Fin c)) : (final ns q).2 ≤ budget c := by
  cases q <;> simp only [final,budget] <;> omega
theorem data_bound (q r : Option (Fin c)) : (data ns q r).2 ≤ budget c := by
  cases q with
  | none => cases r with
    | none => simp only [data,budget]; omega
    | some r =>
      have ha := StoredRunTable.any_bound c (firstTerm ns r) 19 (fun _ => le_rfl)
      simp only [data,budget]; omega
  | some q => cases r <;> simp only [data,budget] <;> omega

theorem initial_shape (q : Option (Fin c)) : nodes (initial ns q).1 ≤ sizeBudget c ∧ arity (initial ns q).1 ≤ 1 := by
  cases q <;> exact ⟨by simp only [initial,nodes,sizeBudget]; omega,by simp only [initial,final,data,arity]; exact Nat.zero_le 1⟩
theorem final_shape (q : Option (Fin c)) : nodes (final ns q).1 ≤ sizeBudget c ∧ arity (final ns q).1 ≤ 1 := by
  cases q <;> exact ⟨by simp only [final,nodes,sizeBudget]; omega,by simp only [initial,final,data,arity]; exact Nat.zero_le 1⟩
theorem firstTerm_shape (r q : Fin c) : nodes (firstTerm ns r q).1 ≤ 7 ∧ arity (firstTerm ns r q).1 ≤ 1 := by
  simp only [firstTerm,StoredArrayEquality.conj,block,nodes,arity]; exact ⟨le_rfl,le_rfl⟩
theorem data_shape (q r : Option (Fin c)) : nodes (data ns q r).1 ≤ sizeBudget c ∧ arity (data ns q r).1 ≤ 1 := by
  cases q with
  | none => cases r with
    | none => exact ⟨by simp only [data,nodes,sizeBudget]; omega,by simp only [initial,final,data,arity]; exact Nat.zero_le 1⟩
    | some r =>
      have hn := StoredRawSwitchGuard.any_nodes_bound c (firstTerm ns r) 7 (fun q => (firstTerm_shape ns r q).1)
      have hk := StoredRunTable.any_arity_le c (firstTerm ns r) 1 (fun q => (firstTerm_shape ns r q).2)
      constructor
      · simp only [data,StoredArrayEquality.conj,noA,nodes,sizeBudget]; omega
      · exact StoredRunTable.conj_arity_le _ _ 1 le_rfl hk
  | some q => cases r with
    | none => exact ⟨by simp only [data,nodes,sizeBudget]; omega,by simp only [initial,final,data,arity]; exact Nat.zero_le 1⟩
    | some r =>
      simp only [data,StoredArrayEquality.conj,noA,block,nodes,arity,sizeBudget]
      exact ⟨by omega,le_rfl⟩

theorem initial_qf (q : Option (Fin c)) : (denote (initial ns q).1).IsQF := by
  rw [initial_value]
  obtain ⟨i,hi⟩ := BlockCandidateTransport.stateAt_surjective c q
  simpa only [BlockCandidateTransport.compile,hi] using (RankNextQuantifierFree.candidate_qf ns c).initial i
theorem final_qf (q : Option (Fin c)) : (denote (final ns q).1).IsQF := by
  rw [final_value]
  obtain ⟨i,hi⟩ := BlockCandidateTransport.stateAt_surjective c q
  simpa only [BlockCandidateTransport.compile,hi] using (RankNextQuantifierFree.candidate_qf ns c).final i
theorem data_qf (q r : Option (Fin c)) : (denote (data ns q r).1).IsQF := by
  rw [data_value]
  obtain ⟨i,hi⟩ := BlockCandidateTransport.stateAt_surjective c q
  obtain ⟨j,hj⟩ := BlockCandidateTransport.stateAt_surjective c r
  simpa only [BlockCandidateTransport.compile,hi,hj] using (RankNextQuantifierFree.candidate_qf ns c).data i j
end NSSE.StoredNextCandidateGuards
