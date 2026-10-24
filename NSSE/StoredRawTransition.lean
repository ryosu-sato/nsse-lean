import NSSE.StoredRawSwitchGuard

/-! All four actual phase transitions of a guarded raw row. -/
namespace NSSE.StoredRawTransition
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow ConvolutionShapes StoredRawBackGuards
variable {R : Nat → Type} {P : Type} {n : Nat}
abbrev State (n : Nat) := Bool × (Fin n × Fin n)

def build (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) : Data R (Params P s) 0 × Nat :=
  let a := match q.1,r.1 with
    | false,false => shared A s q.2 r.2
    | false,true => StoredRawSwitchGuard.build A s q.2 r.2 seed last first
    | true,true => pair A s q.2 r.2
    | true,false => (.falsum,1)
  (a.1,2+a.2)
theorem value (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) :
    denote (build A s seed last first q r).1 = A.original.stepGuard s seed last first q r := by
  obtain ⟨bq,q⟩ := q
  obtain ⟨br,r⟩ := r
  cases bq <;> cases br <;>
    simp only [build,shared_value,StoredRawSwitchGuard.value,pair_value,denote,SymbolicGuardedBlocks.Row.stepGuard]
  all_goals rfl
def budget (n B K : Nat) := 3+sharedBudget n B K+StoredRawSwitchGuard.budget n B K+pairBudget n B K
def sizeBudget (n B : Nat) := 29+4*B+StoredRawSwitchGuard.sizeBudget n B

theorem bound (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) (B K : Nat) (h : Bounds A B K) :
    (build A s seed last first q r).2 ≤ budget n B K := by
  have hs := shared_bound A s q.2 r.2 B K h
  have hw := StoredRawSwitchGuard.bound A s q.2 r.2 seed last first B K h
  have hp := pair_bound A s q.2 r.2 B K h
  obtain ⟨bq,q⟩ := q
  obtain ⟨br,r⟩ := r
  cases bq <;> cases br <;> simp only [build,budget] at * <;> omega

theorem shape (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) (B K : Nat) (h : Bounds A B K) :
    nodes (build A s seed last first q r).1 ≤ sizeBudget n B ∧ arity (build A s seed last first q r).1 ≤ K := by
  have hs := shared_shape A s q.2 r.2 B K h
  have hw := StoredRawSwitchGuard.shape A s q.2 r.2 seed last first B K h
  have hp := pair_shape A s q.2 r.2 B K h
  obtain ⟨bq,q⟩ := q
  obtain ⟨br,r⟩ := r
  cases bq <;> cases br <;> simp only [build,sizeBudget,nodes,StoredRelationalFormula.arity] at *
  all_goals constructor <;> omega

theorem qfree (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) :
    (denote (build A s seed last first q r).1).IsQF := by
  rw [value]
  obtain ⟨bq,q⟩ := q
  obtain ⟨br,r⟩ := r
  cases bq <;> cases br <;> simp only [SymbolicGuardedBlocks.Row.stepGuard]
  · exact ExactGuardedRunFormula.sharedGuard_qf A.original A.qfree.toRowQF s q r
  · exact ExactGuardedRunFormula.switchGuard_qf A.original A.qfree.toRowQF s q r seed last first
  · exact BoundedFormula.isQF_bot
  · exact (ExactGuardedRunFormula.backGuard_qf A.original A.qfree.toRowQF s q.1 r.1 0).inf
      (ExactGuardedRunFormula.backGuard_qf A.original A.qfree.toRowQF s q.2 r.2 1)

def label (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) : QF R (Params P s) × Nat :=
  let a := build A s seed last first q r
  (⟨a.1,qfree A s seed last first q r⟩,1+a.2)
theorem label_bounds (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (q r : State n) (B K : Nat) (h : Bounds A B K) :
    StoredRunTable.LabelBound (label A s seed last first q r) (1+budget n B K) (sizeBudget n B) K := by
  have hc := bound A s seed last first q r B K h
  have hs := shape A s seed last first q r B K h
  exact ⟨by simp only [label]; omega,hs.1,hs.2⟩
end NSSE.StoredRawTransition
