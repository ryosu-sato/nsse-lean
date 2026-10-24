import NSSE.StoredRowTransport
import NSSE.StoredRawSwitchGuard
import NSSE.DirectEmptyTailRemoval

/-! Counted stored labels for the actual empty-tail compiler used by direct cleanup. -/
namespace NSSE.StoredEmptyTailGuards
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n : Nat}
abbrev State (n : Nat) := EmptyTailAutomaton.State (Fin n)

def term (A : Row R P n) (q r z : Fin n) : Data R (P ⊕ Fin 1) 0 × Nat :=
  let a := readPair A.data q z
  let b := readPair A.left z r
  let c := rename (fun p => ((Sum.inl p : P ⊕ Fin 1),1)) b.1.formula
  (StoredArrayEquality.conj a.1.formula c.1,8+a.2+b.2+c.2)
theorem term_value (A : Row R P n) (q r z : Fin n) :
    denote (term A q r z).1 = A.original.data q z ⊓ (A.original.left z r).relabel Sum.inl := by
  simp only [term,StoredArrayEquality.conj,denote,formula_value,Row.original]; rfl
def termBudget (n B K : Nat) := 10+4*n+weight K 1*B
theorem term_bound (A : Row R P n) (q r z : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (term A q r z).2 ≤ termBudget n B K := by
  have ha := readPair_bound A.data q z
  have hb := readPair_bound A.left z r
  have hc := rename_bound (fun p => ((Sum.inl p : P ⊕ Fin 1),1)) 1 K (fun _ => le_rfl)
    (readPair A.left z r).1.formula (h.left_arity z r)
  have hn := h.left z r
  simp only [term,termBudget]; nlinarith
theorem term_shape (A : Row R P n) (q r z : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (term A q r z).1 ≤ 5+2*B ∧ arity (term A q r z).1 ≤ K := by
  constructor
  · have ha := h.data q z; have hb := h.left z r
    simp only [term,StoredArrayEquality.conj,nodes,rename_nodes]; omega
  · apply StoredRunTable.conj_arity_le
    · exact h.data_arity q z
    · rw [rename_arity]; exact h.left_arity z r

def switch (A : Row R P n) (last : P) (q r : Fin n) : Data R (P ⊕ Fin 1) 0 × Nat :=
  let a := rename (StoredRawSwitchGuard.guardName (.inr 0) (.inl last)) A.guard.formula
  let b := StoredRunTable.any n (term A q r)
  (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem switch_value (A : Row R P n) (last : P) (q r : Fin n) :
    denote (switch A last q r).1 = EmptyTailFiring.switchGuard A.original last q r := by
  simp only [switch,StoredArrayEquality.conj,denote,formula_value,StoredRawSwitchGuard.guardName_value,
    StoredRunTable.any_value,term_value,EmptyTailFiring.switchGuard,SymbolicGuardedBlocks.guardAt,Row.original]; rfl
def switchBudget (n B K : Nat) := 7+weight K 2*B+StoredRunTable.anyBudget n (termBudget n B K)
def switchSize (n B : Nat) := 6+B+n*(8+2*B)
theorem switch_bound (A : Row R P n) (last : P) (q r : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (switch A last q r).2 ≤ switchBudget n B K := by
  have ha := rename_bound (StoredRawSwitchGuard.guardName (P := P) (.inr (0 : Fin 1)) (.inl last))
    2 K (StoredRawSwitchGuard.guardName_bound _ _) A.guard.formula h.guard_arity
  have hb := StoredRunTable.any_bound n (term A q r) _ (fun z => term_bound A q r z B K h)
  have hn := h.guard
  simp only [switch,switchBudget]; nlinarith
theorem switch_shape (A : Row R P n) (last : P) (q r : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (switch A last q r).1 ≤ switchSize n B ∧ arity (switch A last q r).1 ≤ K := by
  have hn := StoredRawSwitchGuard.any_nodes_bound n (term A q r) (5+2*B) (fun z => (term_shape A q r z B K h).1)
  constructor
  · have hg := h.guard
    simp only [switch,StoredArrayEquality.conj,nodes,rename_nodes,switchSize]; nlinarith
  · apply StoredRunTable.conj_arity_le
    · rw [rename_arity]; exact h.guard_arity
    · exact StoredRunTable.any_arity_le n _ K (fun z => (term_shape A q r z B K h).2)

def finalTerm (A : Row R P n) (q r : Fin n) : Data R P 0 × Nat :=
  let a := readPair A.right q r
  let b := StoredRelationTuple.read A.final r
  (StoredArrayEquality.conj a.1.formula b.1.formula,7+a.2+b.2)
theorem finalTerm_value (A : Row R P n) (q r : Fin n) :
    denote (finalTerm A q r).1 = A.original.right q r ⊓ A.original.final r := by
  simp only [finalTerm,StoredArrayEquality.conj,denote,Row.original]; rfl
theorem finalTerm_bound (A : Row R P n) (q r : Fin n) : (finalTerm A q r).2 ≤ 8+3*n := by
  have ha := readPair_bound A.right q r
  have hb := StoredRelationTuple.read_bound A.final r
  simp only [finalTerm]; omega
theorem finalTerm_shape (A : Row R P n) (q r : Fin n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (finalTerm A q r).1 ≤ 5+2*B ∧ arity (finalTerm A q r).1 ≤ K := by
  constructor
  · have ha := h.right q r; have hb := h.final r
    simp only [finalTerm,StoredArrayEquality.conj,nodes]; omega
  · exact StoredRunTable.conj_arity_le _ _ K (h.right_arity q r) (h.final_arity r)

def initial (A : Row R P n) : State n → Data R P 0 × Nat
  | .before q => let a := StoredRelationTuple.read A.initial q; (a.1.formula,1+a.2)
  | _ => (.falsum,2)
def final (A : Row R P n) : State n → Data R P 0 × Nat
  | .after q => let a := StoredRunTable.any n (finalTerm A q); (a.1,1+a.2)
  | _ => (.falsum,2)
def data (A : Row R P n) (last : P) : State n → State n → Data R (P ⊕ Fin 1) 0 × Nat
  | .before q, .before r | .needAfter q, .after r | .after q, .after r =>
      let a := readPair A.data q r; (a.1.formula,2+a.2)
  | .before q, .needAfter r => let a := switch A last q r; (a.1,2+a.2)
  | _, _ => (.falsum,3)
theorem initial_value (A : Row R P n) (q : State n) :
    denote (initial A q).1 = EmptyTailFiring.initialGuard A.original q := by cases q <;> rfl
theorem final_value (A : Row R P n) (q : State n) :
    denote (final A q).1 = EmptyTailFiring.finalGuard A.original q := by
  cases q <;> simp only [final,EmptyTailFiring.finalGuard,StoredRunTable.any_value,finalTerm_value]; all_goals rfl
theorem data_value (A : Row R P n) (last : P) (q r : State n) :
    denote (data A last q r).1 = EmptyTailFiring.dataGuard A.original last q r := by
  cases q <;> cases r <;> simp only [data,EmptyTailFiring.dataGuard,switch_value]; all_goals rfl

def costBudget (n B K : Nat) := 5+2*n+switchBudget n B K+StoredRunTable.anyBudget n (8+3*n)
def sizeBudget (n B : Nat) := switchSize n B

theorem initial_bound (A : Row R P n) (q : State n) (B K : Nat) :
    (initial A q).2 ≤ costBudget n B K := by
  cases q with
  | before q => have h := StoredRelationTuple.read_bound A.initial q; simp only [initial,costBudget]; omega
  | needAfter q | after q => simp only [initial,costBudget]; omega
theorem final_bound (A : Row R P n) (q : State n) (B K : Nat) :
    (final A q).2 ≤ costBudget n B K := by
  cases q with
  | after q => have h := StoredRunTable.any_bound n (finalTerm A q) _ (finalTerm_bound A q); simp only [final,costBudget]; omega
  | before q | needAfter q => simp only [final,costBudget]; omega
theorem data_bound (A : Row R P n) (last : P) (q r : State n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (data A last q r).2 ≤ costBudget n B K := by
  cases q <;> cases r <;> rename_i q r <;> simp only [data,costBudget]
  all_goals first | omega | (have ht := readPair_bound A.data q r; omega) |
    (have ht := switch_bound A last q r B K h; omega)
theorem initial_shape (A : Row R P n) (q : State n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (initial A q).1 ≤ sizeBudget n B ∧ arity (initial A q).1 ≤ K := by
  cases q with
  | before q => have hn := h.initial q; exact ⟨by simp only [initial,sizeBudget,switchSize]; omega,h.initial_arity q⟩
  | needAfter q | after q => exact ⟨by simp only [initial,nodes,sizeBudget,switchSize]; omega,Nat.zero_le K⟩
theorem final_shape (A : Row R P n) (q : State n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (final A q).1 ≤ sizeBudget n B ∧ arity (final A q).1 ≤ K := by
  cases q with
  | after q =>
    have hn := StoredRawSwitchGuard.any_nodes_bound n (finalTerm A q) (5+2*B) (fun r => (finalTerm_shape A q r B K h).1)
    exact ⟨by simp only [final,sizeBudget,switchSize]; nlinarith,
      StoredRunTable.any_arity_le n _ K (fun r => (finalTerm_shape A q r B K h).2)⟩
  | before q | needAfter q => exact ⟨by simp only [final,nodes,sizeBudget,switchSize]; omega,Nat.zero_le K⟩
theorem data_shape (A : Row R P n) (last : P) (q r : State n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    nodes (data A last q r).1 ≤ sizeBudget n B ∧ arity (data A last q r).1 ≤ K := by
  cases q <;> cases r <;> rename_i q r <;> simp only [data]
  all_goals first | exact switch_shape A last _ _ B K h |
    exact ⟨by simp only [nodes,sizeBudget,switchSize]; omega,Nat.zero_le K⟩ |
    (have hn := h.data q r; exact ⟨by simp only [sizeBudget,switchSize]; omega,h.data_arity _ _⟩)
theorem initial_qf (A : Row R P n) (q : State n) : (denote (initial A q).1).IsQF := by
  rw [initial_value]
  cases q
  · exact A.qfree.initial _
  · exact .falsum
  · exact .falsum
theorem final_qf (A : Row R P n) (q : State n) : (denote (final A q).1).IsQF := by
  rw [final_value]
  cases q
  · exact .falsum
  · exact .falsum
  · exact ExactReachabilityTable.any_qf n _ (fun r => (A.qfree.right _ r).inf (A.qfree.final r))
theorem data_qf (A : Row R P n) (last : P) (q r : State n) : (denote (data A last q r).1).IsQF := by
  rw [data_value]
  cases q <;> cases r <;> simp only [EmptyTailFiring.dataGuard]
  all_goals first | exact A.qfree.data _ _ | exact BoundedFormula.isQF_bot |
    exact (ExactReachabilityTable.relabel_qf _ A.qfree.guard _).inf
      (ExactReachabilityTable.any_qf n _ (fun z => (A.qfree.data _ z).inf
        (ExactReachabilityTable.relabel_qf _ (A.qfree.left z _) _)))
end NSSE.StoredEmptyTailGuards
