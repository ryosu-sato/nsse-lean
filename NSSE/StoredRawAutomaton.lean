import NSSE.StoredRawStates

/-! Guarded raw automata with a counted state table and counted label callbacks. -/
namespace NSSE.StoredRawAutomaton
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow StoredRawBackGuards
variable {R : Nat → Type} {P : Type} {n : Nat}

def make (A : Row R P n) (table : StoredRawStates.Table n) (e : SymbolicGuardedBlocks.Ends n)
    (seed last : P) (first : Bool) : StoredDynamicColumn.Automaton R P table.count where
  initial i :=
    let q := StoredRawStates.read table i
    let f := StoredRawEndpoints.initialLabel A e last q.1
    (f.1,1+q.2+f.2)
  final i :=
    let q := StoredRawStates.read table i
    let f := StoredRawEndpoints.finalLabel A e seed last first q.1
    (f.1,1+q.2+f.2)
  step s i j :=
    let q := StoredRawStates.read table i
    let r := StoredRawStates.read table j
    let f := StoredRawTransition.label A s seed last first q.1 r.1
    (f.1,2+q.2+r.2+f.2)

/-- Semantic view only: transport the original raw numbering along the
proved computed dimension. No original state enumeration runs in make. -/
def original (A : Row R P n) (table : StoredRawStates.Table n) (e : SymbolicGuardedBlocks.Ends n)
    (seed last : P) (first : Bool) : ConvolutionShapes.WordAutomaton (UniformWordLowering.wordLanguage R) P table.count 2 where
  initial i := (A.original.raw e seed last first).initial (Fin.cast table.count_eq i)
  final i := (A.original.raw e seed last first).final (Fin.cast table.count_eq i)
  silent _ _ := ⊥
  step s i j := (A.original.raw e seed last first).step s (Fin.cast table.count_eq i) (Fin.cast table.count_eq j)

theorem value (A : Row R P n) (table : StoredRawStates.Table n) (e : SymbolicGuardedBlocks.Ends n)
    (seed last : P) (first : Bool) : (make A table e seed last first).original = original A table e seed last first := by
  simp only [make,StoredDynamicColumn.Automaton.original,StoredRawEndpoints.initialLabel,StoredRawEndpoints.finalLabel,
    StoredRawTransition.label,StoredRawEndpoints.initial_value,StoredRawEndpoints.final_value,StoredRawTransition.value,
    StoredRawStates.read_value,original,SymbolicGuardedBlocks.Row.raw]
  congr 1
  funext s i j
  exact StoredRawTransition.value A s seed last first _ _

def costBudget (n B K : Nat) := 4+4*n*n+StoredRawEndpoints.initialBudget n B K+
  StoredRawEndpoints.finalBudget n B K+StoredRawTransition.budget n B K
def nodeBudget (n B : Nat) := 15+5*B+StoredRawTransition.sizeBudget n B

theorem bounds (A : Row R P n) (table : StoredRawStates.Table n) (e : SymbolicGuardedBlocks.Ends n)
    (seed last : P) (first : Bool) (B K : Nat) (h : Bounds A B K) :
    StoredDynamicColumn.Bounds (make A table e seed last first) (costBudget n B K) (nodeBudget n B) K := by
  constructor
  · intro i
    have hr := StoredRawStates.read_bound table i
    have hf := StoredRawEndpoints.initialLabel_bound A e last (StoredRawStates.read table i).1 B K h
    refine ⟨?_,?_,hf.arity⟩
    · have hc := hf.cost
      simp only [make,costBudget]; nlinarith
    · have hn := hf.nodes
      change nodes (StoredRawEndpoints.initialLabel A e last (StoredRawStates.read table i).1).1.formula ≤ _
      unfold nodeBudget; omega
  · intro i
    have hr := StoredRawStates.read_bound table i
    have hf := StoredRawEndpoints.finalLabel_bound A e seed last first (StoredRawStates.read table i).1 B K h
    refine ⟨?_,?_,hf.arity⟩
    · have hc := hf.cost
      simp only [make,costBudget]; nlinarith
    · have hn := hf.nodes
      change nodes (StoredRawEndpoints.finalLabel A e seed last first (StoredRawStates.read table i).1).1.formula ≤ _
      unfold nodeBudget; omega
  · intro s i j
    have hi := StoredRawStates.read_bound table i
    have hj := StoredRawStates.read_bound table j
    have hf := StoredRawTransition.label_bounds A s seed last first (StoredRawStates.read table i).1 (StoredRawStates.read table j).1 B K h
    refine ⟨?_,?_,hf.arity⟩
    · have hc := hf.cost
      simp only [make,costBudget]; nlinarith
    · have hn := hf.nodes
      change nodes (StoredRawTransition.label A s seed last first (StoredRawStates.read table i).1 (StoredRawStates.read table j).1).1.formula ≤ _
      unfold nodeBudget; omega

structure Built (R : Nat → Type) (P : Type) (n : Nat) where
  table : StoredRawStates.Table n
  automaton : StoredDynamicColumn.Automaton R P table.count

def build (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) : Built R P n × Nat :=
  let a := StoredRawStates.build n
  (⟨a.1,make A a.1 e seed last first⟩,1+a.2)
theorem build_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    (build A e seed last first).2 ≤ 1+StoredRawStates.budget n := by
  have h := StoredRawStates.bound n
  simp only [build]; omega
theorem build_bounds (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (B K : Nat) (h : Bounds A B K) :
    StoredDynamicColumn.Bounds (build A e seed last first).1.automaton (costBudget n B K) (nodeBudget n B) K :=
  bounds A (StoredRawStates.build n).1 e seed last first B K h
end NSSE.StoredRawAutomaton
