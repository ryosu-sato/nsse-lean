import NSSE.StoredRowComplementStates

/-! Counted conjunction and truth cells over actual stored Boolean masks. -/
namespace NSSE.StoredTruthCell
open FirstOrder FirstOrder.Language StoredRelationalFormula
variable {R : Nat → Type} {P : Type}

theorem fold_shape (xs : List (Data R P 0)) (B K : Nat)
    (h : ∀ f ∈ xs, nodes f ≤ B ∧ arity f ≤ K) :
    nodes (StoredArrayEquality.fold xs).1 ≤ 3+xs.length*(5+B) ∧ arity (StoredArrayEquality.fold xs).1 ≤ K := by
  induction xs with
  | nil => exact ⟨by simp [StoredArrayEquality.fold,nodes],Nat.zero_le K⟩
  | cons f xs ih =>
    have hf := h f (by simp)
    have ht := ih (fun g hg => h g (by simp [hg]))
    constructor
    · simp only [StoredArrayEquality.fold,StoredArrayEquality.conj,nodes,List.length_cons]; nlinarith
    · exact StoredRunTable.conj_arity_le _ _ K hf.2 ht.2

def all (n : Nat) (f : Fin n → Data R P 0 × Nat) :=
  let a := CountedFinEnumeration.tabulate n f
  let b := StoredArrayEquality.fold a.1
  (b.1,1+a.2+b.2)
theorem all_value (n : Nat) (f : Fin n → Data R P 0 × Nat) :
    denote (all n f).1 = SymbolicComplement.all n (fun i => denote (f i).1) := by
  simp only [all,StoredArrayEquality.fold_value,CountedFinEnumeration.tabulate_value,
    List.map_ofFn,List.ofFn_eq_map,SymbolicComplement.all,List.map_map]; rfl
def allBudget (n c : Nat) := 4+StoredForwardTableBuild.tabBudget n c+6*n
theorem all_bound (n : Nat) (f : Fin n → Data R P 0 × Nat) (c : Nat) (h : ∀ i, (f i).2 ≤ c) :
    (all n f).2 ≤ allBudget n c := by
  have ha := CountedFinEnumeration.tabulate_bound n f c h
  simp only [all,StoredArrayEquality.fold_cost,CountedFinEnumeration.tabulate_value,List.length_ofFn,allBudget,StoredForwardTableBuild.tabBudget] at *; omega
theorem all_shape (n : Nat) (f : Fin n → Data R P 0 × Nat) (B K : Nat)
    (h : ∀ i, nodes (f i).1 ≤ B ∧ arity (f i).1 ≤ K) :
    nodes (all n f).1 ≤ 3+n*(5+B) ∧ arity (all n f).1 ≤ K := by
  have hf := fold_shape (CountedFinEnumeration.tabulate n f).1 B K (by
    intro g hg
    simp only [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hg
    obtain ⟨i,rfl⟩ := hg
    exact h i)
  simpa only [all,CountedFinEnumeration.tabulate_value,List.length_ofFn] using hf

def signed {n : Nat} (s : List Bool) (f : Fin n → Data R P 0 × Nat) (i : Fin n) :=
  let b := StoredRowComplementStates.bit s i
  let a := f i
  if b.1 then (a.1,2+b.2+a.2) else (.imp a.1 .falsum,4+b.2+a.2)
theorem signed_value {n : Nat} (s : List Bool) (f : Fin n → Data R P 0 × Nat) (i : Fin n) :
    denote (signed s f i).1 = if StoredForwardSubset.denote n s i then denote (f i).1 else (denote (f i).1).not := by
  simp only [signed,StoredRowComplementStates.bit_value]; split <;> rfl
theorem signed_bound {n : Nat} (s : List Bool) (f : Fin n → Data R P 0 × Nat) (i : Fin n)
    (c : Nat) (h : (f i).2 ≤ c) : (signed s f i).2 ≤ 4+n+c := by
  have hb := StoredRowComplementStates.bit_bound s i
  simp only [signed]; split <;> omega
theorem signed_shape {n : Nat} (s : List Bool) (f : Fin n → Data R P 0 × Nat) (i : Fin n)
    (B K : Nat) (h : nodes (f i).1 ≤ B ∧ arity (f i).1 ≤ K) :
    nodes (signed s f i).1 ≤ B+2 ∧ arity (signed s f i).1 ≤ K := by
  simp only [signed]; split <;> dsimp only
  · exact ⟨by omega,h.2⟩
  · simp only [nodes,arity,Nat.max_zero]; exact ⟨by omega,h.2⟩

def build (n : Nat) (s : List Bool) (f : Fin n → Data R P 0 × Nat) := all n (signed s f)
theorem value (n : Nat) (s : List Bool) (f : Fin n → Data R P 0 × Nat) :
    denote (build n s f).1 = SymbolicComplement.cell (StoredForwardSubset.denote n s) (fun i => denote (f i).1) := by
  simp only [build,all_value,signed_value,SymbolicComplement.cell]
def budget (n c : Nat) := allBudget n (4+n+c)
theorem bound (n : Nat) (s : List Bool) (f : Fin n → Data R P 0 × Nat) (c : Nat) (h : ∀ i, (f i).2 ≤ c) :
    (build n s f).2 ≤ budget n c := all_bound n _ _ (fun i => signed_bound s f i c (h i))
theorem shape (n : Nat) (s : List Bool) (f : Fin n → Data R P 0 × Nat) (B K : Nat)
    (h : ∀ i, nodes (f i).1 ≤ B ∧ arity (f i).1 ≤ K) :
    nodes (build n s f).1 ≤ 3+n*(7+B) ∧ arity (build n s f).1 ≤ K := by
  have ht := all_shape n (signed s f) (B+2) K (fun i => signed_shape s f i B K (h i))
  simpa only [build,show 5+(B+2)=7+B by omega] using ht
end NSSE.StoredTruthCell
