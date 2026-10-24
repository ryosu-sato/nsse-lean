import NSSE.StoredRowComplementGuards

/-! Actual stored direct complement construction, with table reads and label production counted. -/
namespace NSSE.StoredRowComplementCompiler
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n : Nat}

def initial (S : StoredRowComplementStates.Table n) (A : Row R P n) (i : Fin S.count) : QF R P × Nat :=
  let q := StoredRowComplementStates.read S i
  let a := StoredRowComplementGuards.initial (R := R) (P := P) q.1
  (⟨a.1,StoredRowComplementGuards.initial_qf A q.1⟩,2+q.2+a.2)
def final (S : StoredRowComplementStates.Table n) (A : Row R P n) (i : Fin S.count) : QF R P × Nat :=
  let q := StoredRowComplementStates.read S i
  let a := StoredRowComplementGuards.final A q.1
  (⟨a.1,StoredRowComplementGuards.final_qf A q.1⟩,2+q.2+a.2)
def data (S : StoredRowComplementStates.Table n) (A : Row R P n) (i j : Fin S.count) : QF R (P ⊕ Fin 1) × Nat :=
  let q := StoredRowComplementStates.read S i
  let r := StoredRowComplementStates.read S j
  let a := StoredRowComplementGuards.step A q.1 r.1
  (⟨a.1,StoredRowComplementGuards.step_qf A q.1 r.1⟩,3+q.2+r.2+a.2)
def matrix {Q : Type} (m : Nat) (f : Fin m → Fin m → QF R Q × Nat) :=
  StoredRelationTuple.tabulate (fun i => StoredRelationTuple.tabulate (f i))
def labels (S : StoredRowComplementStates.Table n) (A : Row R P n) : Row R P S.count × Nat :=
  let a := StoredRelationTuple.tabulate (initial S A)
  let b := StoredRelationTuple.tabulate (final S A)
  let c := matrix S.count (data S A)
  let d := matrix S.count (fun _ _ => ((⟨.falsum,.falsum⟩ : QF R P),2))
  (⟨a.1,b.1,c.1,d.1,d.1,⟨.falsum,.falsum⟩⟩,7+a.2+b.2+c.2+d.2)

theorem matrix_read {Q : Type} (m : Nat) (f : Fin m → Fin m → QF R Q × Nat) (i j : Fin m) :
    (readPair (matrix m f).1 i j).1 = (f i j).1 := by
  simp only [matrix,readPair,StoredRelationTuple.tabulate_read]
theorem value (S : StoredRowComplementStates.Table n) (A : Row R P n) :
    (labels S A).1.original =
      { initial := fun i => (DirectRowBooleanOperations.complement A.original).initial (Fin.cast S.count_eq i)
        final := fun i => (DirectRowBooleanOperations.complement A.original).final (Fin.cast S.count_eq i)
        data := fun i j => (DirectRowBooleanOperations.complement A.original).data (Fin.cast S.count_eq i) (Fin.cast S.count_eq j)
        left := fun _ _ => ⊥
        right := fun _ _ => ⊥
        guard := ⊥ } := by
  unfold Row.original labels
  simp only [StoredRelationTuple.tabulate_read,matrix_read,initial,final,data,
    StoredRowComplementGuards.initial_value A,StoredRowComplementGuards.final_value,StoredRowComplementGuards.step_value,
    StoredRowComplementStates.read_value,DirectRowBooleanOperations.complement]
  rfl

def vertexCost (n B K : Nat) := 2+(2^n+1)+StoredRowComplementGuards.budget n B K
def edgeCost (n B K : Nat) := 3+2*(2^n+1)+StoredRowComplementGuards.budget n B K
def vectorBudget (m c : Nat) := 1+StoredForwardTableBuild.tabBudget m c
def matrixBudget (m c : Nat) := vectorBudget m (vectorBudget m c)
def labelBudget (n B K : Nat) := 7+2*vectorBudget ((2^n+1)) (vertexCost n B K)+
  matrixBudget ((2^n+1)) (edgeCost n B K)+matrixBudget ((2^n+1)) 2

theorem matrix_bound {Q : Type} (m : Nat) (f : Fin m → Fin m → QF R Q × Nat) (c : Nat)
    (h : ∀ i j, (f i j).2 ≤ c) : (matrix m f).2 ≤ matrixBudget m c :=
  StoredRelationTuple.tabulate_bound _ _ (fun i => StoredRelationTuple.tabulate_bound _ _ (h i))
theorem labels_bound (S : StoredRowComplementStates.Table n) (A : Row R P n)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) : (labels S A).2 ≤ labelBudget n B K := by
  have hi (i : Fin S.count) : (initial S A i).2 ≤ vertexCost n B K := by
    have hs := StoredRowComplementStates.read_bound S i
    have ha := StoredRowComplementGuards.initial_bound (R := R) (P := P) (StoredRowComplementStates.read S i).1 n B K
    simp only [initial,vertexCost]; omega
  have hf (i : Fin S.count) : (final S A i).2 ≤ vertexCost n B K := by
    have hs := StoredRowComplementStates.read_bound S i
    have ha := StoredRowComplementGuards.final_bound A (StoredRowComplementStates.read S i).1 B K
    simp only [final,vertexCost]; omega
  have hd (i j : Fin S.count) : (data S A i j).2 ≤ edgeCost n B K := by
    have hs := StoredRowComplementStates.read_bound S i
    have ht := StoredRowComplementStates.read_bound S j
    have ha := StoredRowComplementGuards.step_bound A (StoredRowComplementStates.read S i).1
      (StoredRowComplementStates.read S j).1 B K h
    simp only [data,edgeCost]; omega
  have ha := StoredRelationTuple.tabulate_bound _ _ hi
  have hb := StoredRelationTuple.tabulate_bound _ _ hf
  have hc := matrix_bound S.count (data S A) _ hd
  have he := matrix_bound (R := R) (Q := P) S.count (fun _ _ => (⟨.falsum,.falsum⟩,2)) 2 (fun _ _ => le_rfl)
  conv at ha => rhs; rw [StoredRowComplementStates.count_value S]
  conv at hb => rhs; rw [StoredRowComplementStates.count_value S]
  conv at hc => rhs; rw [StoredRowComplementStates.count_value S]
  conv at he => rhs; rw [StoredRowComplementStates.count_value S]
  simp only [labels,labelBudget,vectorBudget] at *; omega

structure Result (R : Nat → Type) (P : Type) (n : Nat) where
  states : StoredRowComplementStates.Table n
  row : Row R P states.count

def build (A : Row R P n) : Result R P n × Nat :=
  let s := StoredRowComplementStates.build n
  let a := labels s.1 A
  (⟨s.1,a.1⟩,2+s.2+a.2)
def budget (n B K : Nat) := 2+StoredRowComplementStates.budget n+labelBudget n B K
theorem bound (A : Row R P n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (build A).2 ≤ budget n B K := by
  have hs := StoredRowComplementStates.bound n
  have ha := labels_bound (StoredRowComplementStates.build n).1 A B K h
  simp only [build,budget]; omega
theorem labels_shape (S : StoredRowComplementStates.Table n) (A : Row R P n)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (labels S A).1 (StoredRowComplementGuards.sizeBudget n B) K := by
  constructor
  · constructor
    · intro q r
      simpa only [labels,matrix_read,data] using (StoredRowComplementGuards.step_shape A
        (StoredRowComplementStates.read S q).1 (StoredRowComplementStates.read S r).1 B K h).1
    · intro q r; simp only [labels,matrix_read,nodes,StoredRowComplementGuards.sizeBudget,StoredRowComplementGuards.sumSize]; omega
    · intro q r; simp only [labels,matrix_read,nodes,StoredRowComplementGuards.sizeBudget,StoredRowComplementGuards.sumSize]; omega
    · simp only [labels,nodes,StoredRowComplementGuards.sizeBudget,StoredRowComplementGuards.sumSize]; omega
    · intro q r
      simpa only [labels,matrix_read,data] using (StoredRowComplementGuards.step_shape A
        (StoredRowComplementStates.read S q).1 (StoredRowComplementStates.read S r).1 B K h).2
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le K
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le K
    · exact Nat.zero_le K
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredRowComplementGuards.initial_shape (R := R) (P := P) (StoredRowComplementStates.read S q).1 n B K).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredRowComplementGuards.final_shape A (StoredRowComplementStates.read S q).1 B K h).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredRowComplementGuards.initial_shape (R := R) (P := P) (StoredRowComplementStates.read S q).1 n B K).2
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredRowComplementGuards.final_shape A (StoredRowComplementStates.read S q).1 B K h).2

theorem shape (A : Row R P n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (build A).1.row (StoredRowComplementGuards.sizeBudget n B) K :=
  labels_shape _ A B K h

theorem accepts (A : Row R P n)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build A).1.row.original.dataNFA p).Accepts xs ↔ ¬ (A.original.dataNFA p).Accepts xs := by
  let S := (StoredRowComplementStates.build n).1
  have he : ((labels S A).1.original.dataNFA p) =
      SymbolicComplement.pullback ((DirectRowBooleanOperations.complement A.original).dataNFA p) (Fin.cast S.count_eq) := by
    rw [value]; rfl
  change ((labels S A).1.original.dataNFA p).Accepts xs ↔ _
  have hs : Function.Surjective (Fin.cast S.count_eq) := fun j => ⟨Fin.cast S.count_eq.symm j,Fin.ext rfl⟩
  rw [he,SymbolicComplement.pullback_accepts _ _ hs,
    DirectRowBooleanOperations.complement_correct]
end NSSE.StoredRowComplementCompiler
