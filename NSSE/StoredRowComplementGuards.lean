import NSSE.StoredTruthCell

/-! Actual truth-cell labels of direct row complement. All mask and row reads are counted. -/
namespace NSSE.StoredRowComplementGuards
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n : Nat}

def firstTerm (A : Row R P n) (r q : Fin n) : Data R (P ⊕ Fin 1) 0 × Nat :=
  let a := StoredRelationTuple.read A.initial q
  let b := readPair A.data q r
  let c := rename (fun p => ((Sum.inl p : P ⊕ Fin 1),1)) a.1.formula
  (StoredArrayEquality.conj c.1 b.1.formula,8+a.2+b.2+c.2)
def nextTerm (A : Row R P n) (s : List Bool) (r q : Fin n) : Data R (P ⊕ Fin 1) 0 × Nat :=
  let b := StoredRowComplementStates.bit s q
  if b.1 then
    let a := readPair A.data q r
    (a.1.formula,2+b.2+a.2)
  else (.falsum,2+b.2)
def finalTerm (A : Row R P n) : Option (List Bool) → Fin n → Data R P 0 × Nat
  | none,q =>
    let a := StoredRelationTuple.read A.initial q
    let b := StoredRelationTuple.read A.final q
    (StoredArrayEquality.conj a.1.formula b.1.formula,7+a.2+b.2)
  | some s,q =>
    let b := StoredRowComplementStates.bit s q
    if b.1 then let a := StoredRelationTuple.read A.final q; (a.1.formula,2+b.2+a.2)
    else (.falsum,2+b.2)

theorem firstTerm_value (A : Row R P n) (r q : Fin n) :
    denote (firstTerm A r q).1 = (A.original.initial q).relabel Sum.inl ⊓ A.original.data q r := by
  simp only [firstTerm,StoredArrayEquality.conj,denote,formula_value,Row.original]; rfl
theorem nextTerm_value (A : Row R P n) (s : List Bool) (r q : Fin n) :
    denote (nextTerm A s r q).1 = if StoredForwardSubset.denote n s q then A.original.data q r else ⊥ := by
  simp only [nextTerm,StoredRowComplementStates.bit_value]; split <;> rfl

def termBudget (n B K : Nat) := 9+3*n+weight K 1*B
def termSize (B : Nat) := 5+2*B
theorem firstTerm_bound (A : Row R P n) (r q : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (firstTerm A r q).2 ≤ termBudget n B K := by
  have ha := StoredRelationTuple.read_bound A.initial q
  have hb := readPair_bound A.data q r
  have hc := rename_bound (fun p => ((Sum.inl p : P ⊕ Fin 1),1)) 1 K (fun _ => le_rfl)
    (StoredRelationTuple.read A.initial q).1.formula (h.initial_arity q)
  have hn := h.initial q
  simp only [firstTerm,termBudget]; nlinarith
theorem firstTerm_shape (A : Row R P n) (r q : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (firstTerm A r q).1 ≤ termSize B ∧ arity (firstTerm A r q).1 ≤ K := by
  constructor
  · have ha := h.initial q; have hb := h.data q r
    simp only [firstTerm,StoredArrayEquality.conj,nodes,rename_nodes,termSize]; omega
  · apply StoredRunTable.conj_arity_le
    · rw [rename_arity]; exact h.initial_arity q
    · exact h.data_arity q r
theorem nextTerm_bound (A : Row R P n) (s : List Bool) (r q : Fin n) (B K : Nat) :
    (nextTerm A s r q).2 ≤ termBudget n B K := by
  have hb := StoredRowComplementStates.bit_bound s q
  have ha := readPair_bound A.data q r
  simp only [nextTerm]; split <;> dsimp only <;> unfold termBudget <;> omega
theorem nextTerm_shape (A : Row R P n) (s : List Bool) (r q : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (nextTerm A s r q).1 ≤ termSize B ∧ arity (nextTerm A s r q).1 ≤ K := by
  simp only [nextTerm]; split <;> dsimp only
  · exact ⟨by have ha := h.data q r; unfold termSize; omega,h.data_arity q r⟩
  · exact ⟨by simp only [nodes,termSize]; omega,Nat.zero_le K⟩
theorem finalTerm_bound (A : Row R P n) (s : Option (List Bool)) (q : Fin n) (B K : Nat) :
    (finalTerm A s q).2 ≤ termBudget n B K := by
  have ha := StoredRelationTuple.read_bound A.initial q
  have hf := StoredRelationTuple.read_bound A.final q
  cases s with
  | none => simp only [finalTerm,termBudget]; omega
  | some s =>
    have hb := StoredRowComplementStates.bit_bound s q
    simp only [finalTerm]; split <;> dsimp only <;> unfold termBudget <;> omega
theorem finalTerm_shape (A : Row R P n) (s : Option (List Bool)) (q : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (finalTerm A s q).1 ≤ termSize B ∧ arity (finalTerm A s q).1 ≤ K := by
  cases s with
  | none =>
    constructor
    · have hi := h.initial q; have hf := h.final q
      simp only [finalTerm,StoredArrayEquality.conj,nodes,termSize]; omega
    · exact StoredRunTable.conj_arity_le _ _ K (h.initial_arity q) (h.final_arity q)
  | some s =>
    simp only [finalTerm]; split <;> dsimp only
    · exact ⟨by have hf := h.final q; unfold termSize; omega,h.final_arity q⟩
    · exact ⟨by simp only [nodes,termSize]; omega,Nat.zero_le K⟩

def first (A : Row R P n) (r : Fin n) := StoredRunTable.any n (firstTerm A r)
def next (A : Row R P n) (s : List Bool) (r : Fin n) := StoredRunTable.any n (nextTerm A s r)
def finalBase (A : Row R P n) (s : Option (List Bool)) := StoredRunTable.any n (finalTerm A s)
theorem first_value (A : Row R P n) (r : Fin n) :
    denote (first A r).1 = SymbolicComplement.first (RowRegularOperations.toAutomaton A.original) 0 r := by
  simp only [first,StoredRunTable.any_value,firstTerm_value,SymbolicComplement.first,RowRegularOperations.toAutomaton]
theorem next_value (A : Row R P n) (s : List Bool) (r : Fin n) :
    denote (next A s r).1 = SymbolicComplement.next (RowRegularOperations.toAutomaton A.original) (StoredForwardSubset.denote n s) 0 r := by
  simp only [next,StoredRunTable.any_value,nextTerm_value,SymbolicComplement.next,RowRegularOperations.toAutomaton]
theorem finalBase_value (A : Row R P n) (s : Option (List Bool)) :
    denote (finalBase A s).1 = SymbolicComplement.finalGuard (RowRegularOperations.toAutomaton A.original) (StoredRowComplementStates.denote n s) := by
  cases s with
  | none => simp only [finalBase,StoredRunTable.any_value,finalTerm,StoredArrayEquality.conj,denote,
      SymbolicComplement.finalGuard,StoredRowComplementStates.denote,RowRegularOperations.toAutomaton,Row.original]; rfl
  | some s =>
    simp only [finalBase,StoredRunTable.any_value,finalTerm,StoredRowComplementStates.bit_value,
      SymbolicComplement.finalGuard,StoredRowComplementStates.denote,RowRegularOperations.toAutomaton,Row.original]
    congr 1; funext q; split <;> rfl

def sumBudget (n B K : Nat) := StoredRunTable.anyBudget n (termBudget n B K)
def sumSize (n B : Nat) := 1+n*(3+termSize B)
theorem first_bound (A : Row R P n) (r : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (first A r).2 ≤ sumBudget n B K := StoredRunTable.any_bound _ _ _ (fun q => firstTerm_bound A r q B K h)
theorem next_bound (A : Row R P n) (s : List Bool) (r : Fin n) (B K : Nat) :
    (next A s r).2 ≤ sumBudget n B K := StoredRunTable.any_bound _ _ _ (fun q => nextTerm_bound A s r q B K)
theorem finalBase_bound (A : Row R P n) (s : Option (List Bool)) (B K : Nat) :
    (finalBase A s).2 ≤ sumBudget n B K := StoredRunTable.any_bound _ _ _ (fun q => finalTerm_bound A s q B K)

theorem first_shape (A : Row R P n) (r : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (first A r).1 ≤ sumSize n B ∧ arity (first A r).1 ≤ K :=
  ⟨StoredRawSwitchGuard.any_nodes_bound _ _ _ (fun q => (firstTerm_shape A r q B K h).1),
    StoredRunTable.any_arity_le _ _ _ (fun q => (firstTerm_shape A r q B K h).2)⟩
theorem next_shape (A : Row R P n) (s : List Bool) (r : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (next A s r).1 ≤ sumSize n B ∧ arity (next A s r).1 ≤ K :=
  ⟨StoredRawSwitchGuard.any_nodes_bound _ _ _ (fun q => (nextTerm_shape A s r q B K h).1),
    StoredRunTable.any_arity_le _ _ _ (fun q => (nextTerm_shape A s r q B K h).2)⟩
theorem finalBase_shape (A : Row R P n) (s : Option (List Bool)) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (finalBase A s).1 ≤ sumSize n B ∧ arity (finalBase A s).1 ≤ K :=
  ⟨StoredRawSwitchGuard.any_nodes_bound _ _ _ (fun q => (finalTerm_shape A s q B K h).1),
    StoredRunTable.any_arity_le _ _ _ (fun q => (finalTerm_shape A s q B K h).2)⟩

def initial (s : Option (List Bool)) : Data R P 0 × Nat :=
  match s with | none => (.imp .falsum .falsum,3) | some _ => (.falsum,2)
def final (A : Row R P n) (s : Option (List Bool)) : Data R P 0 × Nat :=
  let a := finalBase A s
  (.imp a.1 .falsum,3+a.2)
def step (A : Row R P n) : Option (List Bool) → Option (List Bool) → Data R (P ⊕ Fin 1) 0 × Nat
  | _,none => (.falsum,2)
  | none,some t => let a := StoredTruthCell.build n t (first A); (a.1,2+a.2)
  | some s,some t => let a := StoredTruthCell.build n t (next A s); (a.1,2+a.2)
theorem initial_value (A : Row R P n) (s : Option (List Bool)) :
    denote (initial (R := R) (P := P) s).1 = SymbolicComplement.startGuard (RowRegularOperations.toAutomaton A.original) (StoredRowComplementStates.denote n s) := by
  cases s <;> rfl
theorem final_value (A : Row R P n) (s : Option (List Bool)) :
    denote (final A s).1 = (SymbolicComplement.finalGuard (RowRegularOperations.toAutomaton A.original) (StoredRowComplementStates.denote n s)).not := by
  simp only [final,denote,finalBase_value]; rfl
theorem step_value (A : Row R P n) (s t : Option (List Bool)) :
    denote (step A s t).1 = SymbolicComplement.stepGuard (RowRegularOperations.toAutomaton A.original) 0
      (StoredRowComplementStates.denote n s) (StoredRowComplementStates.denote n t) := by
  cases s <;> cases t <;> simp only [step,StoredTruthCell.value,first_value,next_value,
    SymbolicComplement.stepGuard,StoredRowComplementStates.denote]; all_goals rfl

def budget (n B K : Nat) := 5+sumBudget n B K+StoredTruthCell.budget n (sumBudget n B K)
def sizeBudget (n B : Nat) := 6+sumSize n B+n*(7+sumSize n B)
theorem initial_bound (s : Option (List Bool)) (n B K : Nat) : (initial (R := R) (P := P) s).2 ≤ budget n B K := by
  cases s <;> simp only [initial,budget] <;> omega
theorem final_bound (A : Row R P n) (s : Option (List Bool)) (B K : Nat) : (final A s).2 ≤ budget n B K := by
  have ha := finalBase_bound A s B K
  simp only [final,budget]; omega
theorem step_bound (A : Row R P n) (s t : Option (List Bool)) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (step A s t).2 ≤ budget n B K := by
  cases s with
  | none => cases t with
    | none => simp only [step,budget]; omega
    | some t =>
      have ha := StoredTruthCell.bound n t (first A) _ (fun r => first_bound A r B K h)
      simp only [step,budget]; omega
  | some s => cases t with
    | none => simp only [step,budget]; omega
    | some t =>
      have ha := StoredTruthCell.bound n t (next A s) _ (fun r => next_bound A s r B K)
      simp only [step,budget]; omega

theorem initial_shape (s : Option (List Bool)) (n B K : Nat) :
    nodes (initial (R := R) (P := P) s).1 ≤ sizeBudget n B ∧ arity (initial (R := R) (P := P) s).1 ≤ K := by
  cases s <;> exact ⟨by simp only [initial,nodes,sizeBudget]; omega,Nat.zero_le K⟩
theorem final_shape (A : Row R P n) (s : Option (List Bool)) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (final A s).1 ≤ sizeBudget n B ∧ arity (final A s).1 ≤ K := by
  have ha := finalBase_shape A s B K h
  simp only [final,nodes,arity,Nat.max_zero,sizeBudget]; exact ⟨by omega,ha.2⟩
theorem step_shape (A : Row R P n) (s t : Option (List Bool)) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (step A s t).1 ≤ sizeBudget n B ∧ arity (step A s t).1 ≤ K := by
  cases s with
  | none => cases t with
    | none => exact ⟨by simp only [step,nodes,sizeBudget]; omega,Nat.zero_le K⟩
    | some t =>
      have ha := StoredTruthCell.shape n t (first A) (sumSize n B) K (fun r => first_shape A r B K h)
      exact ⟨by simp only [step,sizeBudget]; omega,ha.2⟩
  | some s => cases t with
    | none => exact ⟨by simp only [step,nodes,sizeBudget]; omega,Nat.zero_le K⟩
    | some t =>
      have ha := StoredTruthCell.shape n t (next A s) (sumSize n B) K (fun r => next_shape A s r B K h)
      exact ⟨by simp only [step,sizeBudget]; omega,ha.2⟩
theorem initial_qf (A : Row R P n) (s : Option (List Bool)) : (denote (initial (R := R) (P := P) s).1).IsQF := by
  rw [initial_value A]
  obtain ⟨i,hi⟩ := SymbolicComplement.decodeState_surjective n (StoredRowComplementStates.denote n s)
  simpa only [DirectRowBooleanOperations.complement,hi] using
    (DirectRowBooleanOperations.complement_qf A.original A.qfree).initial i
theorem final_qf (A : Row R P n) (s : Option (List Bool)) : (denote (final A s).1).IsQF := by
  rw [final_value]
  obtain ⟨i,hi⟩ := SymbolicComplement.decodeState_surjective n (StoredRowComplementStates.denote n s)
  simpa only [DirectRowBooleanOperations.complement,hi] using
    (DirectRowBooleanOperations.complement_qf A.original A.qfree).final i
theorem step_qf (A : Row R P n) (s t : Option (List Bool)) : (denote (step A s t).1).IsQF := by
  rw [step_value]
  obtain ⟨i,hi⟩ := SymbolicComplement.decodeState_surjective n (StoredRowComplementStates.denote n s)
  obtain ⟨j,hj⟩ := SymbolicComplement.decodeState_surjective n (StoredRowComplementStates.denote n t)
  simpa only [DirectRowBooleanOperations.complement,hi,hj] using
    (DirectRowBooleanOperations.complement_qf A.original A.qfree).data i j
end NSSE.StoredRowComplementGuards
