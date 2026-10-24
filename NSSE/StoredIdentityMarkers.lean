import NSSE.StoredGuardedArrayPackage

/-! Counted identity marker matrices for original block atoms. -/
namespace NSSE.StoredIdentityMarkers
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n : Nat}

def entry (i j : Fin n) : QF R P × Nat :=
  let e := FiniteValuationLookup.equalNat i.val j.val
  let f := StoredRelationalReachability.literal e.1
  (⟨f.1,StoredRelationalReachability.literal_qf e.1⟩,2+e.2+f.2)
theorem entry_value (i j : Fin n) : denote (entry (R := R) (P := P) i j).1.formula =
    BlockRelationPresentation.identityGuard i j := by
  simp only [entry,StoredRawBackGuards.literal_value,StoredRawBackGuards.equal_value,decide_eq_true_eq,
    BlockRelationPresentation.identityGuard]
theorem entry_bound (i j : Fin n) : (entry (R := R) (P := P) i j).2 ≤ 5+n := by
  have he := FiniteValuationLookup.equalNat_bound i.val j.val
  have hf := StoredRelationalReachability.literal_shape (R := R) (P := P) (FiniteValuationLookup.equalNat i.val j.val).1
  simp only [entry]; omega

def matrix (n : Nat) : StoredRelationalRow.Vector (StoredRelationalRow.Vector (QF R P) n) n × Nat :=
  StoredRelationTuple.tabulate fun i => StoredRelationTuple.tabulate (entry i)
theorem matrix_read (i j : Fin n) : (readPair (matrix (R := R) (P := P) n).1 i j).1 = (entry i j).1 := by
  simp only [matrix,readPair,StoredRelationTuple.tabulate_read]
def matrixBudget (n : Nat) := 1+StoredForwardTableBuild.tabBudget n (1+StoredForwardTableBuild.tabBudget n (5+n))
theorem matrix_bound (n : Nat) : (matrix (R := R) (P := P) n).2 ≤ matrixBudget n := by
  apply StoredRelationTuple.tabulate_bound
  intro i
  exact StoredRelationTuple.tabulate_bound (entry i) (5+n) (entry_bound i)

def build (A : Row R P n) : Row R P n × Nat :=
  let m := matrix n
  let g := StoredRelationalReachability.literal (R := R) (P := P ⊕ Fin 2) true
  (⟨A.initial,A.final,A.data,m.1,m.1,⟨g.1,StoredRelationalReachability.literal_qf true⟩⟩,4+m.2+g.2)
theorem value (A : Row R P n) : (build A).1.original = BlockRelationPresentation.identityMarkers A.original := by
  simp only [build,Row.original,matrix_read,entry_value,StoredRawBackGuards.literal_value,
    BlockRelationPresentation.identityMarkers,↓reduceIte]
def budget (n : Nat) := 7+matrixBudget n
theorem bound (A : Row R P n) : (build A).2 ≤ budget n := by
  have h := matrix_bound (R := R) (P := P) n
  simp only [build,budget,StoredRelationalReachability.literal]; omega

theorem preserves (A : Row R P n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (build A).1 (B+3) K := by
  have he (i j : Fin n) : nodes (entry (R := R) (P := P) i j).1.formula ≤ 3 ∧
      arity (entry (R := R) (P := P) i j).1.formula = 0 :=
    (StoredRelationalReachability.literal_shape _).2
  constructor
  · constructor
    · intro i j; have := h.data i j; change nodes (readPair A.data i j).1.formula ≤ _; omega
    · intro i j; simpa only [build,matrix_read] using (he i j).1.trans (Nat.le_add_left 3 B)
    · intro i j; simpa only [build,matrix_read] using (he i j).1.trans (Nat.le_add_left 3 B)
    · change 3 ≤ B+3; omega
    · exact h.data_arity
    · intro i j; simp only [build,matrix_read,(he i j).2]; omega
    · intro i j; simp only [build,matrix_read,(he i j).2]; omega
    · change 0 ≤ K; omega
  · intro i; have := h.initial i; change nodes (StoredRelationTuple.read A.initial i).1.formula ≤ _; omega
  · intro i; have := h.final i; change nodes (StoredRelationTuple.read A.final i).1.formula ≤ _; omega
  · exact h.initial_arity
  · exact h.final_arity
end NSSE.StoredIdentityMarkers
