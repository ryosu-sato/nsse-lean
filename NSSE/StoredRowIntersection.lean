import NSSE.StoredRowProductStates

/-! Counted direct row intersection from stored formula fields, with no silent closure. -/
namespace NSSE.StoredRowIntersection
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
open StoredEmptyTailCompiler (matrix matrix_read matrix_bound matrixBudget vectorBudget)
variable {R : Nat → Type} {P : Type} {n m : Nat}

def conj (a b : QF R P) : QF R P × Nat :=
  (⟨StoredArrayEquality.conj a.formula b.formula,by
    change (denote a.formula ⊓ denote b.formula).IsQF
    exact a.qfree.inf b.qfree⟩,7)
theorem conj_value (a b : QF R P) : denote (conj a b).1.formula = denote a.formula ⊓ denote b.formula := rfl
theorem conj_shape (a b : QF R P) :
    nodes (conj a b).1.formula = 5+nodes a.formula+nodes b.formula ∧
    arity (conj a b).1.formula = max (arity a.formula) (arity b.formula) := by
  simp only [conj,StoredArrayEquality.conj,nodes,arity]
  omega

def vertex (S : StoredRowProductStates.Table n m) (a : StoredRelationalRow.Vector (QF R P) n)
    (b : StoredRelationalRow.Vector (QF R P) m) (i : Fin S.count) : QF R P × Nat :=
  let q := StoredRowProductStates.read S i
  let x := StoredRelationTuple.read a q.1.1
  let y := StoredRelationTuple.read b q.1.2
  let f := conj x.1 y.1
  (f.1,3+q.2+x.2+y.2+f.2)
def edge (S : StoredRowProductStates.Table n m) (A : Row R P n) (B : Row R P m) (i j : Fin S.count) : QF R (P ⊕ Fin 1) × Nat :=
  let q := StoredRowProductStates.read S i
  let r := StoredRowProductStates.read S j
  let x := readPair A.data q.1.1 r.1.1
  let y := readPair B.data q.1.2 r.1.2
  let f := conj x.1 y.1
  (f.1,4+q.2+r.2+x.2+y.2+f.2)
def labels (S : StoredRowProductStates.Table n m) (A : Row R P n) (B : Row R P m) : Row R P S.count × Nat :=
  let a := StoredRelationTuple.tabulate (vertex S A.initial B.initial)
  let b := StoredRelationTuple.tabulate (vertex S A.final B.final)
  let c := matrix S.count (edge S A B)
  let d := matrix S.count (fun _ _ => ((⟨.falsum,.falsum⟩ : QF R P),2))
  (⟨a.1,b.1,c.1,d.1,d.1,⟨.falsum,.falsum⟩⟩,7+a.2+b.2+c.2+d.2)
theorem value (S : StoredRowProductStates.Table n m) (A : Row R P n) (B : Row R P m) :
    (labels S A B).1.original =
      { initial := fun i => (DirectRowBooleanOperations.intersect A.original B.original).initial (Fin.cast S.count_eq i)
        final := fun i => (DirectRowBooleanOperations.intersect A.original B.original).final (Fin.cast S.count_eq i)
        data := fun i j => (DirectRowBooleanOperations.intersect A.original B.original).data (Fin.cast S.count_eq i) (Fin.cast S.count_eq j)
        left := fun _ _ => ⊥
        right := fun _ _ => ⊥
        guard := ⊥ } := by
  unfold Row.original labels
  simp only [StoredRelationTuple.tabulate_read,matrix_read,vertex,edge,conj_value,
    StoredRowProductStates.read_value,DirectRowBooleanOperations.intersect,Row.original]
  rfl

def labelCost (n m : Nat) := 13+2*n*m+2*n+2*m
def labelBudget (n m : Nat) := 7+2*vectorBudget (n*m) (labelCost n m)+
  matrixBudget (n*m) (labelCost n m)+matrixBudget (n*m) 2
theorem vertex_bound (S : StoredRowProductStates.Table n m) (a : StoredRelationalRow.Vector (QF R P) n)
    (b : StoredRelationalRow.Vector (QF R P) m) (i : Fin S.count) : (vertex S a b i).2 ≤ labelCost n m := by
  have hq := StoredRowProductStates.read_bound S i
  have hx := StoredRelationTuple.read_bound a (StoredRowProductStates.read S i).1.1
  have hy := StoredRelationTuple.read_bound b (StoredRowProductStates.read S i).1.2
  simp only [vertex,conj,labelCost]; nlinarith
theorem edge_bound (S : StoredRowProductStates.Table n m) (A : Row R P n) (B : Row R P m) (i j : Fin S.count) :
    (edge S A B i j).2 ≤ labelCost n m := by
  have hq := StoredRowProductStates.read_bound S i
  have hr := StoredRowProductStates.read_bound S j
  have hx := readPair_bound A.data (StoredRowProductStates.read S i).1.1 (StoredRowProductStates.read S j).1.1
  have hy := readPair_bound B.data (StoredRowProductStates.read S i).1.2 (StoredRowProductStates.read S j).1.2
  simp only [edge,conj,labelCost]; nlinarith

theorem labels_bound (S : StoredRowProductStates.Table n m) (A : Row R P n) (B : Row R P m) :
    (labels S A B).2 ≤ labelBudget n m := by
  have ha := StoredRelationTuple.tabulate_bound _ _ (vertex_bound S A.initial B.initial)
  have hb := StoredRelationTuple.tabulate_bound _ _ (vertex_bound S A.final B.final)
  have hc := matrix_bound S.count (edge S A B) _ (edge_bound S A B)
  have he := matrix_bound (R := R) (Q := P) S.count (fun _ _ => (⟨.falsum,.falsum⟩,2)) 2 (fun _ _ => le_rfl)
  conv at ha => rhs; rw [StoredRowProductStates.count_value S]
  conv at hb => rhs; rw [StoredRowProductStates.count_value S]
  conv at hc => rhs; rw [StoredRowProductStates.count_value S]
  conv at he => rhs; rw [StoredRowProductStates.count_value S]
  simp only [labels,labelBudget,vectorBudget] at *; omega

structure Result (R : Nat → Type) (P : Type) (n m : Nat) where
  states : StoredRowProductStates.Table n m
  row : Row R P states.count

def build (A : Row R P n) (B : Row R P m) : Result R P n m × Nat :=
  let s := StoredRowProductStates.build n m
  let a := labels s.1 A B
  (⟨s.1,a.1⟩,2+s.2+a.2)
def budget (n m : Nat) := 2+StoredRowProductStates.budget n m+labelBudget n m
theorem bound (A : Row R P n) (B : Row R P m) : (build A B).2 ≤ budget n m := by
  have hs := StoredRowProductStates.bound n m
  have ha := labels_bound (StoredRowProductStates.build n m).1 A B
  simp only [build,budget]; omega

theorem accepts (A : Row R P n) (B : Row R P m)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build A B).1.row.original.dataNFA p).Accepts xs ↔
      (A.original.dataNFA p).Accepts xs ∧ (B.original.dataNFA p).Accepts xs := by
  let S := (StoredRowProductStates.build n m).1
  have he : ((labels S A B).1.original.dataNFA p) =
      SymbolicComplement.pullback ((DirectRowBooleanOperations.intersect A.original B.original).dataNFA p) (Fin.cast S.count_eq) := by
    rw [value]; rfl
  change ((labels S A B).1.original.dataNFA p).Accepts xs ↔ _
  have hs : Function.Surjective (Fin.cast S.count_eq) := fun j => ⟨Fin.cast S.count_eq.symm j,Fin.ext rfl⟩
  rw [he,SymbolicComplement.pullback_accepts _ _ hs,DirectRowBooleanOperations.intersect_correct]
theorem conj_bounds (a b : QF R P) (B C K : Nat)
    (ha : nodes a.formula ≤ B) (hb : nodes b.formula ≤ C)
    (hka : arity a.formula ≤ K) (hkb : arity b.formula ≤ K) :
    nodes (conj a b).1.formula ≤ 5+B+C ∧ arity (conj a b).1.formula ≤ K := by
  rw [(conj_shape a b).1,(conj_shape a b).2]
  exact ⟨by omega,max_le hka hkb⟩

theorem labels_shape (S : StoredRowProductStates.Table n m) (A : Row R P n) (B : Row R P m)
    (F G K : Nat) (ha : StoredRowTransport.Bounds A F K) (hb : StoredRowTransport.Bounds B G K) :
    StoredRowTransport.Bounds (labels S A B).1 (5+F+G) K := by
  constructor
  · constructor
    · intro q r
      simp only [labels,matrix_read,edge]
      exact (conj_bounds _ _ F G K (ha.data _ _) (hb.data _ _) (ha.data_arity _ _) (hb.data_arity _ _)).1
    · intro q r; simp only [labels,matrix_read,nodes]; omega
    · intro q r; simp only [labels,matrix_read,nodes]; omega
    · simp only [labels,nodes]; omega
    · intro q r
      simp only [labels,matrix_read,edge]
      exact (conj_bounds _ _ F G K (ha.data _ _) (hb.data _ _) (ha.data_arity _ _) (hb.data_arity _ _)).2
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le K
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le K
    · exact Nat.zero_le K
  · intro q
    simp only [labels,StoredRelationTuple.tabulate_read,vertex]
    exact (conj_bounds _ _ F G K (ha.initial _) (hb.initial _) (ha.initial_arity _) (hb.initial_arity _)).1
  · intro q
    simp only [labels,StoredRelationTuple.tabulate_read,vertex]
    exact (conj_bounds _ _ F G K (ha.final _) (hb.final _) (ha.final_arity _) (hb.final_arity _)).1
  · intro q
    simp only [labels,StoredRelationTuple.tabulate_read,vertex]
    exact (conj_bounds _ _ F G K (ha.initial _) (hb.initial _) (ha.initial_arity _) (hb.initial_arity _)).2
  · intro q
    simp only [labels,StoredRelationTuple.tabulate_read,vertex]
    exact (conj_bounds _ _ F G K (ha.final _) (hb.final _) (ha.final_arity _) (hb.final_arity _)).2

theorem shape (A : Row R P n) (B : Row R P m) (F G K : Nat)
    (ha : StoredRowTransport.Bounds A F K) (hb : StoredRowTransport.Bounds B G K) :
    StoredRowTransport.Bounds (build A B).1.row (5+F+G) K := labels_shape _ A B F G K ha hb
theorem budget_diagonal (u : Nat) : budget u u = 31+9*u+55*u^2+9*u^3+29*u^4+4*u^5+4*u^6 := by
  unfold budget labelBudget matrixBudget vectorBudget labelCost StoredRowProductStates.budget
    StoredRowProductStates.entriesBudget StoredForwardTableBuild.tabBudget
  ring

theorem budget_polynomial (n m : Nat) : budget n m ≤ 141*(n+m+1)^6 := by
  let u := n+m+1
  have hn : n ≤ u := by dsimp [u]; omega
  have hm : m ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hb : budget n m ≤ budget u u := by
    unfold budget labelBudget matrixBudget vectorBudget labelCost StoredRowProductStates.budget
      StoredRowProductStates.entriesBudget StoredForwardTableBuild.tabBudget
    gcongr
  have hp (j : Nat) : u^j ≤ u^(j+1) := by
    simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right (u^j) hu
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  norm_num at h0 h1 h2 h3 h4 h5
  rw [budget_diagonal] at hb
  change budget n m ≤ 141*u^6
  linarith only [hb,h0,h1,h2,h3,h4,h5]

theorem polynomial (A : Row R P n) (B : Row R P m) : (build A B).2 ≤ 141*(n+m+1)^6 :=
  (bound A B).trans (budget_polynomial n m)
end NSSE.StoredRowIntersection
