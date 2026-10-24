import NSSE.StoredEmptyTailStates

/-! Actual stored empty-tail automaton construction, with table reads and label production counted. -/
namespace NSSE.StoredEmptyTailCompiler
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n : Nat}

def initial (S : StoredEmptyTailStates.Table n) (A : Row R P n) (i : Fin S.count) : QF R P × Nat :=
  let q := StoredEmptyTailStates.read S i
  let a := StoredEmptyTailGuards.initial A q.1
  (⟨a.1,StoredEmptyTailGuards.initial_qf A q.1⟩,2+q.2+a.2)
def final (S : StoredEmptyTailStates.Table n) (A : Row R P n) (i : Fin S.count) : QF R P × Nat :=
  let q := StoredEmptyTailStates.read S i
  let a := StoredEmptyTailGuards.final A q.1
  (⟨a.1,StoredEmptyTailGuards.final_qf A q.1⟩,2+q.2+a.2)
def data (S : StoredEmptyTailStates.Table n) (A : Row R P n) (last : P) (i j : Fin S.count) : QF R (P ⊕ Fin 1) × Nat :=
  let q := StoredEmptyTailStates.read S i
  let r := StoredEmptyTailStates.read S j
  let a := StoredEmptyTailGuards.data A last q.1 r.1
  (⟨a.1,StoredEmptyTailGuards.data_qf A last q.1 r.1⟩,3+q.2+r.2+a.2)
def matrix {Q : Type} (m : Nat) (f : Fin m → Fin m → QF R Q × Nat) :=
  StoredRelationTuple.tabulate (fun i => StoredRelationTuple.tabulate (f i))
def labels (S : StoredEmptyTailStates.Table n) (A : Row R P n) (last : P) : Row R P S.count × Nat :=
  let a := StoredRelationTuple.tabulate (initial S A)
  let b := StoredRelationTuple.tabulate (final S A)
  let c := matrix S.count (data S A last)
  let d := matrix S.count (fun _ _ => ((⟨.falsum,.falsum⟩ : QF R P),2))
  (⟨a.1,b.1,c.1,d.1,d.1,⟨.falsum,.falsum⟩⟩,7+a.2+b.2+c.2+d.2)

theorem matrix_read {Q : Type} (m : Nat) (f : Fin m → Fin m → QF R Q × Nat) (i j : Fin m) :
    (readPair (matrix m f).1 i j).1 = (f i j).1 := by
  simp only [matrix,readPair,StoredRelationTuple.tabulate_read]
theorem value (S : StoredEmptyTailStates.Table n) (A : Row R P n) (last : P) :
    (labels S A last).1.original =
      { initial := fun i => (EmptyTailFiring.compile A.original last).initial (Fin.cast S.count_eq i)
        final := fun i => (EmptyTailFiring.compile A.original last).final (Fin.cast S.count_eq i)
        data := fun i j => (EmptyTailFiring.compile A.original last).data (Fin.cast S.count_eq i) (Fin.cast S.count_eq j)
        left := fun _ _ => ⊥
        right := fun _ _ => ⊥
        guard := ⊥ } := by
  unfold Row.original labels
  simp only [StoredRelationTuple.tabulate_read,matrix_read,initial,final,data,
    StoredEmptyTailGuards.initial_value,StoredEmptyTailGuards.final_value,StoredEmptyTailGuards.data_value,
    StoredEmptyTailStates.read_value,EmptyTailFiring.compile]
  rfl

def vertexCost (n B K : Nat) := 2+3*n+StoredEmptyTailGuards.costBudget n B K
def edgeCost (n B K : Nat) := 3+6*n+StoredEmptyTailGuards.costBudget n B K
def vectorBudget (m c : Nat) := 1+StoredForwardTableBuild.tabBudget m c
def matrixBudget (m c : Nat) := vectorBudget m (vectorBudget m c)
def labelBudget (n B K : Nat) := 7+2*vectorBudget (3*n) (vertexCost n B K)+
  matrixBudget (3*n) (edgeCost n B K)+matrixBudget (3*n) 2

theorem matrix_bound {Q : Type} (m : Nat) (f : Fin m → Fin m → QF R Q × Nat) (c : Nat)
    (h : ∀ i j, (f i j).2 ≤ c) : (matrix m f).2 ≤ matrixBudget m c :=
  StoredRelationTuple.tabulate_bound _ _ (fun i => StoredRelationTuple.tabulate_bound _ _ (h i))
theorem labels_bound (S : StoredEmptyTailStates.Table n) (A : Row R P n) (last : P)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) : (labels S A last).2 ≤ labelBudget n B K := by
  have hi (i : Fin S.count) : (initial S A i).2 ≤ vertexCost n B K := by
    have hs := StoredEmptyTailStates.read_bound S i
    have ha := StoredEmptyTailGuards.initial_bound A (StoredEmptyTailStates.read S i).1 B K
    simp only [initial,vertexCost]; omega
  have hf (i : Fin S.count) : (final S A i).2 ≤ vertexCost n B K := by
    have hs := StoredEmptyTailStates.read_bound S i
    have ha := StoredEmptyTailGuards.final_bound A (StoredEmptyTailStates.read S i).1 B K
    simp only [final,vertexCost]; omega
  have hd (i j : Fin S.count) : (data S A last i j).2 ≤ edgeCost n B K := by
    have hs := StoredEmptyTailStates.read_bound S i
    have ht := StoredEmptyTailStates.read_bound S j
    have ha := StoredEmptyTailGuards.data_bound A last (StoredEmptyTailStates.read S i).1
      (StoredEmptyTailStates.read S j).1 B K h
    simp only [data,edgeCost]; omega
  have ha := StoredRelationTuple.tabulate_bound _ _ hi
  have hb := StoredRelationTuple.tabulate_bound _ _ hf
  have hc := matrix_bound S.count (data S A last) _ hd
  have he := matrix_bound (R := R) (Q := P) S.count (fun _ _ => (⟨.falsum,.falsum⟩,2)) 2 (fun _ _ => le_rfl)
  conv at ha => rhs; rw [StoredEmptyTailStates.count_value S]
  conv at hb => rhs; rw [StoredEmptyTailStates.count_value S]
  conv at hc => rhs; rw [StoredEmptyTailStates.count_value S]
  conv at he => rhs; rw [StoredEmptyTailStates.count_value S]
  simp only [labels,labelBudget,vectorBudget] at *; omega

structure Result (R : Nat → Type) (P : Type) (n : Nat) where
  states : StoredEmptyTailStates.Table n
  row : Row R P states.count

def build (A : Row R P n) (last : P) : Result R P n × Nat :=
  let s := StoredEmptyTailStates.build n
  let a := labels s.1 A last
  (⟨s.1,a.1⟩,2+s.2+a.2)
def budget (n B K : Nat) := 2+StoredEmptyTailStates.budget n+labelBudget n B K
theorem bound (A : Row R P n) (last : P) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (build A last).2 ≤ budget n B K := by
  have hs := StoredEmptyTailStates.bound n
  have ha := labels_bound (StoredEmptyTailStates.build n).1 A last B K h
  simp only [build,budget]; omega
theorem labels_shape (S : StoredEmptyTailStates.Table n) (A : Row R P n) (last : P)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (labels S A last).1 (StoredEmptyTailGuards.sizeBudget n B) K := by
  constructor
  · constructor
    · intro q r
      simpa only [labels,matrix_read,data] using (StoredEmptyTailGuards.data_shape A last
        (StoredEmptyTailStates.read S q).1 (StoredEmptyTailStates.read S r).1 B K h).1
    · intro q r; simp only [labels,matrix_read,nodes,StoredEmptyTailGuards.sizeBudget,StoredEmptyTailGuards.switchSize]; omega
    · intro q r; simp only [labels,matrix_read,nodes,StoredEmptyTailGuards.sizeBudget,StoredEmptyTailGuards.switchSize]; omega
    · simp only [labels,nodes,StoredEmptyTailGuards.sizeBudget,StoredEmptyTailGuards.switchSize]; omega
    · intro q r
      simpa only [labels,matrix_read,data] using (StoredEmptyTailGuards.data_shape A last
        (StoredEmptyTailStates.read S q).1 (StoredEmptyTailStates.read S r).1 B K h).2
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le K
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le K
    · exact Nat.zero_le K
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredEmptyTailGuards.initial_shape A (StoredEmptyTailStates.read S q).1 B K h).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredEmptyTailGuards.final_shape A (StoredEmptyTailStates.read S q).1 B K h).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredEmptyTailGuards.initial_shape A (StoredEmptyTailStates.read S q).1 B K h).2
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredEmptyTailGuards.final_shape A (StoredEmptyTailStates.read S q).1 B K h).2

theorem shape (A : Row R P n) (last : P) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (build A last).1.row (StoredEmptyTailGuards.sizeBudget n B) K :=
  labels_shape _ A last B K h

theorem accepts (A : Row R P n) (last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build A last).1.row.original.dataNFA p).Accepts xs ↔ EmptyTailFiring.Witness A.original last p xs := by
  let S := (StoredEmptyTailStates.build n).1
  have he : ((labels S A last).1.original.dataNFA p) =
      SymbolicComplement.pullback ((EmptyTailFiring.compile A.original last).dataNFA p) (Fin.cast S.count_eq) := by
    rw [value]; rfl
  change ((labels S A last).1.original.dataNFA p).Accepts xs ↔ _
  have hs : Function.Surjective (Fin.cast S.count_eq) := fun j => ⟨Fin.cast S.count_eq.symm j,Fin.ext rfl⟩
  rw [he,SymbolicComplement.pullback_accepts _ _ hs,
    EmptyTailFiring.compile_witness]
theorem budget_diagonal (u : Nat) : budget u u u = 31+223*u+598*u^2+585*u^3+180*u^4+27*u^5 := by
  unfold budget labelBudget matrixBudget vectorBudget vertexCost edgeCost
    StoredEmptyTailStates.budget StoredEmptyTailStates.entriesBudget
    StoredEmptyTailGuards.costBudget StoredEmptyTailGuards.switchBudget StoredEmptyTailGuards.termBudget
    StoredRunTable.anyBudget StoredForwardTableBuild.tabBudget weight
  ring

theorem budget_polynomial (n B K : Nat) : budget n B K ≤ 1644*(n+B+K+1)^5 := by
  let u := n+B+K+1
  have hn : n ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hm : budget n B K ≤ budget u u u := by
    unfold budget labelBudget matrixBudget vectorBudget vertexCost edgeCost
      StoredEmptyTailStates.budget StoredEmptyTailStates.entriesBudget
      StoredEmptyTailGuards.costBudget StoredEmptyTailGuards.switchBudget StoredEmptyTailGuards.termBudget
      StoredRunTable.anyBudget StoredForwardTableBuild.tabBudget weight
    gcongr
  have hp (j : Nat) : u^j ≤ u^(j+1) := by
    simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right (u^j) hu
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  norm_num at h0 h1 h2 h3 h4
  rw [budget_diagonal] at hm
  change budget n B K ≤ 1644*u^5
  linarith only [hm,h0,h1,h2,h3,h4]

theorem polynomial (A : Row R P n) (last : P) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (build A last).2 ≤ 1644*(n+B+K+1)^5 :=
  (bound A last B K h).trans (budget_polynomial n B K)
end NSSE.StoredEmptyTailCompiler
