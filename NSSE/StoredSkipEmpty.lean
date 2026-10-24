import NSSE.StoredRawAutomaton
import NSSE.SkipEmptyColumns

/-! Counted empty-column identity transitions on actual stored automata. -/
namespace NSSE.StoredSkipEmpty
open FirstOrder FirstOrder.Language StoredRelationalFormula ConvolutionShapes
variable {R : Nat → Type} {P : Type} {n : Nat}

def present (s : Shape 2) : Bool × Nat :=
  let a := StoredTwoTapeShape.read s 0
  let b := StoredTwoTapeShape.read s 1
  (a.1 || b.1,3+a.2+b.2)
theorem present_value (s : Shape 2) : (present s).1 = maskPresent (mask s) := by
  fin_cases s <;> rfl
theorem present_bound (s : Shape 2) : (present s).2 ≤ 23 := by
  have ha := StoredTwoTapeShape.read_bound s 0
  have hb := StoredTwoTapeShape.read_bound s 1
  simp only [present]; omega

def step (A : StoredDynamicColumn.Automaton R P n) (s : Shape 2) (q r : Fin n) :
    Data R (StoredRawBackGuards.Params P s) 0 × Nat :=
  let p := present s
  if p.1 then
    let a := A.step s q r
    (a.1.formula,2+p.2+a.2)
  else
    let e := FiniteValuationLookup.equalNat q.val r.val
    let f := StoredRelationalReachability.literal e.1
    (f.1,4+p.2+e.2+f.2)
theorem step_value (A : StoredDynamicColumn.Automaton R P n) (s : Shape 2) (q r : Fin n) :
    denote (step A s q r).1 = (SkipEmptyColumns.automaton A.original).step s q r := by
  simp only [step,present_value,SkipEmptyColumns.automaton]
  split
  · rfl
  · simp only [StoredRawBackGuards.literal_value,StoredRawBackGuards.equal_value,decide_eq_true_eq]

theorem step_qf (A : StoredDynamicColumn.Automaton R P n) (s : Shape 2) (q r : Fin n) :
    (denote (step A s q r).1).IsQF := by
  rw [step_value]
  exact SkipEmptyColumns.step_qf A.original (fun s q r => (A.step s q r).1.qfree) s q r

def make (A : StoredDynamicColumn.Automaton R P n) : StoredDynamicColumn.Automaton R P n where
  initial := A.initial
  final := A.final
  step s q r := let a := step A s q r; (⟨a.1,step_qf A s q r⟩,1+a.2)
theorem value (A : StoredDynamicColumn.Automaton R P n) :
    (make A).original = SkipEmptyColumns.automaton A.original := by
  simp only [make,StoredDynamicColumn.Automaton.original]
  congr 1
  funext s q r
  exact step_value A s q r

theorem bounds (A : StoredDynamicColumn.Automaton R P n) (c B K : Nat)
    (h : StoredDynamicColumn.Bounds A c B K) :
    StoredDynamicColumn.Bounds (make A) (31+n+c) (3+B) K := by
  constructor
  · intro q
    have hf := h.initial q
    exact ⟨by have := hf.cost; change (A.initial q).2 ≤ _; omega,
      by have := hf.nodes; change nodes (A.initial q).1.formula ≤ _; omega,hf.arity⟩
  · intro q
    have hf := h.final q
    exact ⟨by have := hf.cost; change (A.final q).2 ≤ _; omega,
      by have := hf.nodes; change nodes (A.final q).1.formula ≤ _; omega,hf.arity⟩
  · intro s q r
    have hp := present_bound s
    have he := FiniteValuationLookup.equalNat_bound q.val r.val
    have hl := StoredRelationalReachability.literal_shape (R := R) (P := StoredRawBackGuards.Params P s)
      (FiniteValuationLookup.equalNat q.val r.val).1
    have hf := h.step s q r
    have hc := hf.cost
    have hn := hf.nodes
    have hk := hf.arity
    constructor
    · change 1+(step A s q r).2 ≤ _
      unfold step; dsimp only; split <;> dsimp only <;> omega
    · change nodes (step A s q r).1 ≤ _
      unfold step; dsimp only; split <;> dsimp only <;> omega
    · change arity (step A s q r).1 ≤ _
      unfold step; dsimp only; split <;> dsimp only <;> omega

theorem accepts (A : StoredDynamicColumn.Automaton R P n) {D : Type}
    [ (UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (w : List (Sparse D 2)) :
    ((make A).original.dataInterpret p).Accepts w ↔
      (A.original.dataInterpret p).Accepts (w.filter (fun c => maskPresent (mask c.1))) := by
  rw [value]
  exact SkipEmptyColumns.data_accepts A.original p w
end NSSE.StoredSkipEmpty
