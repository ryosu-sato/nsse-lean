import NSSE.StoredRowComplementCompiler

/-! Actual counted direct difference, composing complement and intersection. -/
namespace NSSE.StoredRowDifference
open FirstOrder FirstOrder.Language StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n m : Nat}

def build (A : Row R P n) (B : Row R P m) : (Sigma (Row R P)) × Nat :=
  let b := StoredRowComplementCompiler.build B
  let c := StoredRowIntersection.build A b.1.row
  (⟨c.1.states.count,c.1.row⟩,2+b.2+c.2)
def budget (n m G K : Nat) := 2+StoredRowComplementCompiler.budget m G K+
  StoredRowIntersection.budget n (2^m+1)
theorem bound (A : Row R P n) (B : Row R P m) (G K : Nat) (h : StoredRowTransport.Bounds B G K) :
    (build A B).2 ≤ budget n m G K := by
  have hb := StoredRowComplementCompiler.bound B G K h
  have hc := StoredRowIntersection.bound A (StoredRowComplementCompiler.build B).1.row
  conv at hc => rhs; rw [StoredRowComplementStates.count_value]
  simp only [build,budget]; omega
theorem states (A : Row R P n) (B : Row R P m) : (build A B).1.1 = n*(2^m+1) := by
  simp only [build,StoredRowProductStates.count_value,StoredRowComplementStates.count_value]
theorem shape (A : Row R P n) (B : Row R P m) (F G K : Nat)
    (ha : StoredRowTransport.Bounds A F K) (hb : StoredRowTransport.Bounds B G K) :
    StoredRowTransport.Bounds (build A B).1.2 (5+F+StoredRowComplementGuards.sizeBudget m G) K :=
  StoredRowIntersection.shape A (StoredRowComplementCompiler.build B).1.row F _ K ha
    (StoredRowComplementCompiler.shape B G K hb)
theorem accepts (A : Row R P n) (B : Row R P m)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build A B).1.2.original.dataNFA p).Accepts xs ↔
      (A.original.dataNFA p).Accepts xs ∧ ¬ (B.original.dataNFA p).Accepts xs := by
  change ((StoredRowIntersection.build A (StoredRowComplementCompiler.build B).1.row).1.row.original.dataNFA p).Accepts xs ↔ _
  rw [StoredRowIntersection.accepts,StoredRowComplementCompiler.accepts]
end NSSE.StoredRowDifference
