import NSSE.StoredTwoTapeShape

/-! Actual dynamic two-tape column selection with stored relation arguments. -/
namespace NSSE.StoredDynamicColumn
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow ConvolutionShapes
variable {R : Nat → Type} {P : Type} {n : Nat}
abbrev Coordinates (P : Type) := StoredRelationTuple.Data P 2
abbrev Labels (R : Nat → Type) (P : Type) (n : Nat) :=
  (s : Shape 2) → Fin n → Fin n → QF R (P ⊕ Fin (tapes (mask s)).length) × Nat
structure Automaton (R : Nat → Type) (P : Type) (n : Nat) where
  initial : StoredRunTable.Vertex R P n
  final : StoredRunTable.Vertex R P n
  step : Labels R P n

def Automaton.original (A : Automaton R P n) : WordAutomaton (UniformWordLowering.wordLanguage R) P n 2 where
  initial q := denote (A.initial q).1.formula
  final q := denote (A.final q).1.formula
  silent _ _ := ⊥
  step s q r := denote (A.step s q r).1.formula

def selectCell (flags : Coordinates P) (one : P) (s : Shape 2) (i : Fin 2) : Data R P 0 × Nat :=
  let a := StoredTwoTapeShape.read s i
  let b := StoredRelationTuple.read flags i
  let f := Data.equal (Sum.inl b.1) (Sum.inl one)
  (if a.1 then f else .imp f .falsum,7+a.2+b.2)
theorem selectCell_value (flags : Coordinates P) (one : P) (s : Shape 2) (i : Fin 2) :
    denote (selectCell (R := R) flags one s i).1 = ExactReachabilityTable.signed (mask s i)
      (DynamicColumnSelection.flag one (StoredRelationTuple.read flags i).1) := by
  simp only [selectCell,StoredTwoTapeShape.read_value]
  cases mask s i <;> rfl
theorem selectCell_bound (flags : Coordinates P) (one : P) (s : Shape 2) (i : Fin 2) :
    (selectCell (R := R) flags one s i).2 ≤ 19 := by
  have ha := StoredTwoTapeShape.read_bound s i
  have hb := StoredRelationTuple.read_bound flags i
  simp only [selectCell]; omega

def select (flags : Coordinates P) (one : P) (s : Shape 2) : Data R P 0 × Nat :=
  StoredArrayValidity.every 2 (selectCell flags one s)
theorem select_value (flags : Coordinates P) (one : P) (s : Shape 2) :
    denote (select (R := R) flags one s).1 =
      DynamicColumnSelection.select (fun i => (StoredRelationTuple.read flags i).1) one s := by
  simp only [select,StoredArrayValidity.every_value,selectCell_value,DynamicColumnSelection.select]
theorem select_bound (flags : Coordinates P) (one : P) (s : Shape 2) :
    (select (R := R) flags one s).2 ≤ StoredArrayValidity.everyBudget 2 19 :=
  StoredArrayValidity.every_bound 2 _ _ (selectCell_bound flags one s)
theorem select_arity (flags : Coordinates P) (one : P) (s : Shape 2) :
    arity (select (R := R) flags one s).1 = 0 := by
  apply StoredArrayValidity.every_arity
  intro i
  dsimp only [selectCell]
  split <;> rfl

def name (letters : Coordinates P) (s : Shape 2) : P ⊕ Fin (tapes (mask s)).length → P × Nat
  | .inl p => (p,1)
  | .inr i => let a := StoredTwoTapeShape.tape s i
             let b := StoredRelationTuple.read letters a.1
             (b.1,2+a.2+b.2)
theorem name_value (letters : Coordinates P) (s : Shape 2) (x : P ⊕ Fin (tapes (mask s)).length) :
    (name letters s x).1 = Sum.elim id (fun i => (StoredRelationTuple.read letters (tape (mask s) i)).1) x := by
  cases x <;> simp only [name,StoredTwoTapeShape.tape_value,Sum.elim_inl,Sum.elim_inr,id_eq]
theorem name_bound (letters : Coordinates P) (s : Shape 2) (x : P ⊕ Fin (tapes (mask s)).length) :
    (name letters s x).2 ≤ 14 := by
  cases x with
  | inl p => exact (by decide : 1 ≤ 14)
  | inr i =>
    have ha := StoredTwoTapeShape.tape_bound s i
    have hb := StoredRelationTuple.read_bound letters (StoredTwoTapeShape.tape s i).1
    simp only [name]; omega

def cell (A : Labels R P n) (flags letters : Coordinates P) (one : P) (s : Shape 2) (q r : Fin n) : Data R P 0 × Nat :=
  let a := select flags one s
  let b := A s q r
  let c := rename (name letters s) b.1.formula
  (StoredArrayEquality.conj a.1 c.1,8+a.2+b.2+c.2)
theorem cell_value (A : Labels R P n) (flags letters : Coordinates P) (one : P) (s : Shape 2) (q r : Fin n) :
    denote (cell A flags letters one s q r).1 =
      DynamicColumnSelection.select (fun i => (StoredRelationTuple.read flags i).1) one s ⊓
      Formula.relabel (Sum.elim id (fun i => (StoredRelationTuple.read letters (tape (mask s) i)).1))
        (denote (A s q r).1.formula) := by
  simp only [cell,StoredArrayEquality.conj,denote,select_value,formula_value,name_value]
  rfl

def build (A : Labels R P n) (flags letters : Coordinates P) (one : P) (q r : Fin n) : Data R P 0 × Nat :=
  StoredRunTable.any 4 (fun s => cell A flags letters one s q r)
theorem value (A : Automaton R P n) (flags letters : Coordinates P) (one : P) (q r : Fin n) :
    denote (build A.step flags letters one q r).1 = DynamicColumnSelection.step A.original
      (fun i => (StoredRelationTuple.read flags i).1) (fun i => (StoredRelationTuple.read letters i).1) one q r := by
  simp only [build,StoredRunTable.any_value,cell_value,DynamicColumnSelection.step,Automaton.original]
  rfl
theorem qfree (A : Automaton R P n) (flags letters : Coordinates P) (one : P) (q r : Fin n) :
    (denote (build A.step flags letters one q r).1).IsQF := by
  rw [value]
  exact DynamicColumnSelection.step_qf A.original _ _ one (fun s q r => (A.step s q r).1.qfree) q r

structure Bounds (A : Automaton R P n) (c B K : Nat) : Prop where
  initial : ∀ q, StoredRunTable.LabelBound (A.initial q) c B K
  final : ∀ q, StoredRunTable.LabelBound (A.final q) c B K
  step : ∀ s q r, StoredRunTable.LabelBound (A.step s q r) c B K

def cellBudget (c B K : Nat) := 8+StoredArrayValidity.everyBudget 2 19+c+weight K 14*B
theorem cell_bound (A : Labels R P n) (flags letters : Coordinates P) (one : P) (s : Shape 2) (q r : Fin n)
    (c B K : Nat) (h : StoredRunTable.LabelBound (A s q r) c B K) :
    (cell A flags letters one s q r).2 ≤ cellBudget c B K := by
  have ha := select_bound (R := R) flags one s
  have hr := rename_bound (name letters s) 14 K (name_bound letters s) (A s q r).1.formula h.arity
  have hc := h.cost; have hn := h.nodes
  simp only [cell,cellBudget]; nlinarith
def budget (c B K : Nat) := StoredRunTable.anyBudget 4 (cellBudget c B K)
theorem bound (A : Automaton R P n) (flags letters : Coordinates P) (one : P) (q r : Fin n)
    (c B K : Nat) (h : Bounds A c B K) : (build A.step flags letters one q r).2 ≤ budget c B K := by
  have ht := StoredRunTable.any_bound 4
    (fun s => cell A.step flags letters one s q r) _ (fun s => cell_bound A.step flags letters one s q r c B K (h.step s q r))
  exact ht

theorem nodes_bound (A : Automaton R P n) (flags letters : Coordinates P) (one : P) (q r : Fin n)
    (c B K : Nat) (h : Bounds A c B K) : nodes (build A.step flags letters one q r).1 ≤ 109+4*B := by
  rw [← denote_nodes,value]
  have ht := DynamicColumnSelection.nodes_step A.original
    (fun i => (StoredRelationTuple.read flags i).1) (fun i => (StoredRelationTuple.read letters i).1) one
    (G := B) (fun s q r => by change ExactReachabilitySize.nodes (denote (A.step s q r).1.formula) ≤ B
                              rw [denote_nodes]; exact (h.step s q r).nodes) q r
  norm_num only [SymbolicComplement.length_masks] at ht
  nlinarith
theorem arity_bound (A : Automaton R P n) (flags letters : Coordinates P) (one : P) (q r : Fin n)
    (c B K : Nat) (h : Bounds A c B K) : arity (build A.step flags letters one q r).1 ≤ K := by
  apply StoredRunTable.any_arity_le
  intro s
  apply StoredRunTable.conj_arity_le
  · rw [select_arity]; exact Nat.zero_le K
  · rw [rename_arity]; exact (h.step s q r).arity
end NSSE.StoredDynamicColumn
