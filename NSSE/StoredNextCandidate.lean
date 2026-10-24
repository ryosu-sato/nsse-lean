import NSSE.StoredNextCandidateGuards

/-! Actual materialization of the next-rank candidate, with original word semantics. -/
namespace NSSE.StoredNextCandidate
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
open StoredEmptyTailCompiler (matrix matrix_read matrix_bound matrixBudget vectorBudget)
variable {k c : Nat} (ns : Fin k → Nat)

def initial (S : StoredNextCandidateStates.Table c) (i : Fin S.count) : QF (UnifiedBlockPresentation.Rel ns c) Empty × Nat :=
  let q := StoredNextCandidateStates.read S i
  let a := StoredNextCandidateGuards.initial ns q.1
  (⟨a.1,StoredNextCandidateGuards.initial_qf ns q.1⟩,2+q.2+a.2)
def final (S : StoredNextCandidateStates.Table c) (i : Fin S.count) : QF (UnifiedBlockPresentation.Rel ns c) Empty × Nat :=
  let q := StoredNextCandidateStates.read S i
  let a := StoredNextCandidateGuards.final ns q.1
  (⟨a.1,StoredNextCandidateGuards.final_qf ns q.1⟩,2+q.2+a.2)
def data (S : StoredNextCandidateStates.Table c) (i j : Fin S.count) : QF (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) × Nat :=
  let q := StoredNextCandidateStates.read S i
  let r := StoredNextCandidateStates.read S j
  let a := StoredNextCandidateGuards.data ns q.1 r.1
  (⟨a.1,StoredNextCandidateGuards.data_qf ns q.1 r.1⟩,3+q.2+r.2+a.2)
def labels (S : StoredNextCandidateStates.Table c) : Row (UnifiedBlockPresentation.Rel ns c) Empty S.count × Nat :=
  let a := StoredRelationTuple.tabulate (initial ns S)
  let b := StoredRelationTuple.tabulate (final ns S)
  let d := matrix S.count (data ns S)
  let f := matrix S.count (fun _ _ => ((⟨.falsum,.falsum⟩ : QF (UnifiedBlockPresentation.Rel ns c) Empty),2))
  (⟨a.1,b.1,d.1,f.1,f.1,⟨.falsum,.falsum⟩⟩,7+a.2+b.2+d.2+f.2)
theorem value (S : StoredNextCandidateStates.Table c) : (labels ns S).1.original =
    { initial := fun i => (BlockCandidateTransport.compile ns c).initial (Fin.cast S.count_eq i)
      final := fun i => (BlockCandidateTransport.compile ns c).final (Fin.cast S.count_eq i)
      data := fun i j => (BlockCandidateTransport.compile ns c).data (Fin.cast S.count_eq i) (Fin.cast S.count_eq j)
      left := fun _ _ => ⊥
      right := fun _ _ => ⊥
      guard := ⊥ } := by
  unfold Row.original labels
  simp only [StoredRelationTuple.tabulate_read,matrix_read,initial,final,data,
    StoredNextCandidateGuards.initial_value,StoredNextCandidateGuards.final_value,StoredNextCandidateGuards.data_value,
    StoredNextCandidateStates.read_value,BlockCandidateTransport.compile]
  rfl

def vertexCost (c : Nat) := 3+c+StoredNextCandidateGuards.budget c
def edgeCost (c : Nat) := 5+2*c+StoredNextCandidateGuards.budget c
def labelBudget (c : Nat) := 7+2*vectorBudget (c+1) (vertexCost c)+matrixBudget (c+1) (edgeCost c)+matrixBudget (c+1) 2

theorem labels_bound (S : StoredNextCandidateStates.Table c) : (labels ns S).2 ≤ labelBudget c := by
  have hi (i : Fin S.count) : (initial ns S i).2 ≤ vertexCost c := by
    have hq := StoredNextCandidateStates.read_bound S i
    have ha := StoredNextCandidateGuards.initial_bound ns (StoredNextCandidateStates.read S i).1
    simp only [initial,vertexCost]; omega
  have hf (i : Fin S.count) : (final ns S i).2 ≤ vertexCost c := by
    have hq := StoredNextCandidateStates.read_bound S i
    have ha := StoredNextCandidateGuards.final_bound ns (StoredNextCandidateStates.read S i).1
    simp only [final,vertexCost]; omega
  have hd (i j : Fin S.count) : (data ns S i j).2 ≤ edgeCost c := by
    have hq := StoredNextCandidateStates.read_bound S i
    have hr := StoredNextCandidateStates.read_bound S j
    have ha := StoredNextCandidateGuards.data_bound ns (StoredNextCandidateStates.read S i).1 (StoredNextCandidateStates.read S j).1
    simp only [data,edgeCost]; omega
  have ha := StoredRelationTuple.tabulate_bound _ _ hi
  have hb := StoredRelationTuple.tabulate_bound _ _ hf
  have hc := matrix_bound S.count (data ns S) _ hd
  have he := matrix_bound (R := UnifiedBlockPresentation.Rel ns c) (Q := Empty) S.count (fun _ _ => (⟨.falsum,.falsum⟩,2)) 2 (fun _ _ => le_rfl)
  conv at ha => rhs; rw [StoredNextCandidateStates.count_value S]
  conv at hb => rhs; rw [StoredNextCandidateStates.count_value S]
  conv at hc => rhs; rw [StoredNextCandidateStates.count_value S]
  conv at he => rhs; rw [StoredNextCandidateStates.count_value S]
  simp only [labels,labelBudget,vectorBudget] at *; omega

theorem labels_shape (S : StoredNextCandidateStates.Table c) :
    StoredRowTransport.Bounds (labels ns S).1 (StoredNextCandidateGuards.sizeBudget c) 1 := by
  constructor
  · constructor
    · intro q r
      simpa only [labels,matrix_read,data] using
        (StoredNextCandidateGuards.data_shape ns (StoredNextCandidateStates.read S q).1 (StoredNextCandidateStates.read S r).1).1
    · intro q r; simp only [labels,matrix_read,nodes,StoredNextCandidateGuards.sizeBudget]; omega
    · intro q r; simp only [labels,matrix_read,nodes,StoredNextCandidateGuards.sizeBudget]; omega
    · simp only [labels,nodes,StoredNextCandidateGuards.sizeBudget]; omega
    · intro q r
      simpa only [labels,matrix_read,data] using
        (StoredNextCandidateGuards.data_shape ns (StoredNextCandidateStates.read S q).1 (StoredNextCandidateStates.read S r).1).2
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le 1
    · intro q r; simp only [labels,matrix_read,arity]; exact Nat.zero_le 1
    · exact Nat.zero_le 1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredNextCandidateGuards.initial_shape ns (StoredNextCandidateStates.read S q).1).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredNextCandidateGuards.final_shape ns (StoredNextCandidateStates.read S q).1).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredNextCandidateGuards.initial_shape ns (StoredNextCandidateStates.read S q).1).2
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredNextCandidateGuards.final_shape ns (StoredNextCandidateStates.read S q).1).2

structure Result (ns : Fin k → Nat) (c : Nat) where
  states : StoredNextCandidateStates.Table c
  row : Row (UnifiedBlockPresentation.Rel ns c) Empty states.count

def build (c : Nat) : Result ns c × Nat :=
  let s := StoredNextCandidateStates.build c
  let a := labels ns s.1
  (⟨s.1,a.1⟩,2+s.2+a.2)
def budget (c : Nat) := 2+StoredNextCandidateStates.budget c+labelBudget c
theorem bound (c : Nat) : (build ns c).2 ≤ budget c := by
  have hs := StoredNextCandidateStates.bound c
  have ha := labels_bound ns (StoredNextCandidateStates.build c).1
  simp only [build,budget]; omega
theorem shape (c : Nat) : StoredRowTransport.Bounds (build ns c).1.row (StoredNextCandidateGuards.sizeBudget c) 1 :=
  labels_shape ns _

theorem original_accepts (c : Nat) {D : Type} [(UnifiedBlockPresentation.language ns c).Structure D]
    (v : Empty → D) (xs : List D) :
    ((build ns c).1.row.original.dataNFA v).Accepts xs ↔ ((BlockCandidateTransport.compile ns c).dataNFA v).Accepts xs := by
  let S := (StoredNextCandidateStates.build c).1
  have he : (labels ns S).1.original.dataNFA v =
      SymbolicComplement.pullback ((BlockCandidateTransport.compile ns c).dataNFA v) (Fin.cast S.count_eq) := by
    rw [value]; rfl
  change ((labels ns S).1.original.dataNFA v).Accepts xs ↔ _
  rw [he]
  apply SymbolicComplement.pullback_accepts
  exact fun j => ⟨Fin.cast S.count_eq.symm j,Fin.ext rfl⟩

theorem accepts {L : FirstOrder.Language} {P : Type} (rows : (i : Fin k) → SymbolicGuardedBlocks.Row L P (ns i))
    (C : SymbolicGuardedBlocks.Row L P c) (seed last : P) {D : Type} [L.Structure D] (p : P → D)
    (v : Empty → List D) (bs : List (List D)) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    ((build ns c).1.row.original.dataNFA v).Accepts bs ↔
      bs ≠ [] ∧ TerminalCutGeometry.NoA (p last) bs ∧
        (C.dataNFA p).Accepts (p seed :: TerminalBorderRank.decodeBlocks (p last) bs) := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  rw [original_accepts,BlockCandidateTransport.compile_correct]
theorem budget_polynomial (c : Nat) : budget c ≤ 604*(c+1)^4 := by
  have he : budget c = 153+254*c+162*c^2+34*c^3+c^4 := by
    unfold budget labelBudget matrixBudget vectorBudget vertexCost edgeCost StoredNextCandidateGuards.budget
      StoredNextCandidateStates.budget StoredNextCandidateStates.entriesBudget StoredRunTable.anyBudget
      StoredForwardTableBuild.tabBudget
    ring
  rw [he]
  nlinarith [sq_nonneg (c:ℤ)]
theorem polynomial (c : Nat) : (build ns c).2 ≤ 604*(c+1)^4 := (bound ns c).trans (budget_polynomial c)
end NSSE.StoredNextCandidate
