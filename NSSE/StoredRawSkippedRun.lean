import NSSE.StoredSkipEmpty

/-! Raw row generation, empty-column identities and dynamic run closure,
with source guard bounds discharged by actual stored row fields. -/
namespace NSSE.StoredRawSkippedRun
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n T : Nat}

def build (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    StoredRawAutomaton.Built R P n × Nat :=
  let a := StoredRawAutomaton.build A e seed last first
  (⟨a.1.table,StoredSkipEmpty.make a.1.automaton⟩,1+a.2)
theorem build_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    (build A e seed last first).2 ≤ 2+StoredRawStates.budget n := by
  have h := StoredRawAutomaton.build_bound A e seed last first
  simp only [build]; omega

def costBudget (n B K : Nat) := 31+2*n*n+StoredRawAutomaton.costBudget n B K
def nodeBudget (n B : Nat) := 3+StoredRawAutomaton.nodeBudget n B

theorem bounds (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (B K : Nat) (h : StoredRawBackGuards.Bounds A B K) :
    StoredDynamicColumn.Bounds (build A e seed last first).1.automaton (costBudget n B K) (nodeBudget n B) K := by
  have hb := StoredSkipEmpty.bounds (StoredRawAutomaton.build A e seed last first).1.automaton
    (StoredRawAutomaton.costBudget n B K) (StoredRawAutomaton.nodeBudget n B) K
    (StoredRawAutomaton.build_bounds A e seed last first B K h)
  have hn := StoredRawStates.count_value (StoredRawAutomaton.build A e seed last first).1.table
  simp only [hn] at hb
  exact hb

theorem value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    (build A e seed last first).1.automaton.original =
      SkipEmptyColumns.automaton (StoredRawAutomaton.original A (StoredRawStates.build n).1 e seed last first) := by
  simp only [build,StoredSkipEmpty.value,StoredRawAutomaton.build,StoredRawAutomaton.value]

def closed (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (C : StoredDynamicRun.Columns P) (one : P) (T : Nat) (positive : Bool) : Data R P 0 × Nat :=
  let a := build A e seed last first
  let f := StoredDynamicRun.closed a.1.automaton C one T positive
  (f.1,1+a.2+f.2)
theorem closed_value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (C : StoredDynamicRun.Columns P) (one : P) (positive : Bool) :
    denote (closed A e seed last first C one T positive).1 =
      DynamicColumnRunFormula.compile
        (SkipEmptyColumns.automaton (StoredRawAutomaton.original A (StoredRawStates.build n).1 e seed last first))
        (StoredDynamicRun.flags C) (StoredDynamicRun.letters C) one T positive := by
  simp only [closed,StoredDynamicRun.closed_value,value]

def budget (n T d B K : Nat) := 3+StoredRawStates.budget n+
  (1016*661^5)*(2*n*n+T+costBudget n B K+d+nodeBudget n B+K+1)^10

theorem closed_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (C : StoredDynamicRun.Columns P) (one : P) (positive : Bool) (d B K : Nat)
    (h : StoredRawBackGuards.Bounds A B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    (closed A e seed last first C one T positive).2 ≤ budget n T d B K := by
  have hb := StoredDynamicRun.closed_polynomial (build A e seed last first).1.automaton C one positive
    (costBudget n B K) d (nodeBudget n B) K (bounds A e seed last first B K h) hc
  have hn := StoredRawStates.count_value (build A e seed last first).1.table
  simp only [hn] at hb
  have ha := build_bound A e seed last first
  simp only [closed,budget]; omega

theorem closed_correct (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (C : StoredDynamicRun.Columns P) (zero one : P) (positive : Bool) {D : Type}
    [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    Formula.Realize (denote (closed A e seed last first C one T positive).1) p ↔
      (((StoredRawAutomaton.original A (StoredRawStates.build n).1 e seed last first).dataInterpret p).Accepts
        ((DynamicColumnRunFormula.inputWord p (StoredDynamicRun.flags C) (StoredDynamicRun.letters C) one T).filter
          (fun c => ConvolutionShapes.maskPresent (ConvolutionShapes.mask c.1))) ↔ positive = true) := by
  rw [closed_value,DynamicColumnRunFormula.compile_correct _ _ _ zero one T positive p h01,
    SkipEmptyColumns.data_accepts]
end NSSE.StoredRawSkippedRun
