import NSSE.StoredRawBackGuards

/-! Actual stored guarded-row switch formulas, including both state enumerations. -/
namespace NSSE.StoredRawSwitchGuard
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow ConvolutionShapes StoredRawBackGuards
variable {R : Nat → Type} {P : Type} {n : Nat}

def guardName {k : Nat} (x y : P ⊕ Fin k) : P ⊕ Fin 2 → (P ⊕ Fin k) × Nat
  | .inl p => (.inl p,1)
  | .inr i => (if i.val=0 then x else y,2)
theorem guardName_value {k : Nat} (x y : P ⊕ Fin k) (z : P ⊕ Fin 2) :
    (guardName x y z).1 = Sum.elim Sum.inl ![x,y] z := by
  cases z with
  | inl p => rfl
  | inr i => fin_cases i <;> rfl
theorem guardName_bound {k : Nat} (x y : P ⊕ Fin k) (z : P ⊕ Fin 2) : (guardName x y z).2 ≤ 2 := by
  cases z with
  | inl p => exact (by decide : 1 ≤ 2)
  | inr i => exact Nat.le_refl 2

def parameter (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) : Data R (Params P s) 0 × Nat :=
  let x := StoredTwoTapeSlot.valueIndex s 0 (if first then seed else last)
  let y := StoredTwoTapeSlot.valueIndex s 1 last
  let a := rename (guardName x.1 y.1) A.guard.formula
  (a.1,4+x.2+y.2+a.2)
theorem parameter_value (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) :
    denote (parameter A s seed last first).1 = SymbolicGuardedBlocks.guardAt A.original.guard Sum.inl
      (SymbolicGuardedBlocks.Row.valueIndex s 0 (SymbolicGuardedBlocks.fallback seed last first))
      (SymbolicGuardedBlocks.Row.valueIndex s 1 last) := by
  simp only [parameter,formula_value,guardName_value,StoredTwoTapeSlot.valueIndex_value,
    SymbolicGuardedBlocks.guardAt,SymbolicGuardedBlocks.fallback,Row.original]
def parameterBudget (B K : Nat) := 42+weight K 2*B
theorem parameter_bound (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (B K : Nat) (h : Bounds A B K) :
    (parameter A s seed last first).2 ≤ parameterBudget B K := by
  have hx := StoredTwoTapeSlot.valueIndex_bound s 0 (if first then seed else last)
  have hy := StoredTwoTapeSlot.valueIndex_bound s 1 last
  have hr := rename_bound
    (guardName (StoredTwoTapeSlot.valueIndex s 0 (if first then seed else last)).1 (StoredTwoTapeSlot.valueIndex s 1 last).1)
    2 K (guardName_bound _ _) A.guard.formula h.guard_arity
  have hn := h.guard
  simp only [parameter,parameterBudget]; nlinarith
theorem parameter_shape (A : Row R P n) (s : Shape 2) (seed last : P) (first : Bool) (B K : Nat) (h : Bounds A B K) :
    nodes (parameter A s seed last first).1 ≤ B ∧ arity (parameter A s seed last first).1 ≤ K := by
  simp only [parameter,rename_nodes,rename_arity]
  exact ⟨h.guard,h.guard_arity⟩

def term (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (z z' : Fin n) : Data R (Params P s) 0 × Nat :=
  let l := readPair A.left z q.1
  let rr := readPair A.right z' q.2
  let a := rename (fun p => ((Sum.inl p : Params P s),1)) l.1.formula
  let b := rename (fun p => ((Sum.inl p : Params P s),1)) rr.1.formula
  let c := pair A s (z,z') r
  (StoredArrayEquality.conj a.1 (StoredArrayEquality.conj b.1 c.1),17+l.2+rr.2+a.2+b.2+c.2)
theorem term_value (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (z z' : Fin n) :
    denote (term A s q r z z').1 = Formula.relabel Sum.inl (A.original.left z q.1) ⊓
      (Formula.relabel Sum.inl (A.original.right z' q.2) ⊓ A.original.pairBackGuard s (z,z') r) := by
  simp only [term,StoredArrayEquality.conj,denote,formula_value,pair_value,Row.original]
  rfl
def termBudget (n B K : Nat) := 19+4*n+2*weight K 1*B+pairBudget n B K
theorem term_bound (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (z z' : Fin n) (B K : Nat) (h : Bounds A B K) :
    (term A s q r z z').2 ≤ termBudget n B K := by
  have hl := readPair_bound A.left z q.1
  have hr := readPair_bound A.right z' q.2
  have ha := rename_bound (fun p => ((Sum.inl p : Params P s),1)) 1 K (fun _ => le_rfl)
    (readPair A.left z q.1).1.formula (h.left_arity z q.1)
  have hb := rename_bound (fun p => ((Sum.inl p : Params P s),1)) 1 K (fun _ => le_rfl)
    (readPair A.right z' q.2).1.formula (h.right_arity z' q.2)
  have hp := pair_bound A s (z,z') r B K h
  have hla := h.left z q.1
  have hra := h.right z' q.2
  simp only [term,termBudget]; nlinarith
theorem term_shape (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (z z' : Fin n) (B K : Nat) (h : Bounds A B K) :
    nodes (term A s q r z z').1 ≤ 21+4*B ∧ arity (term A s q r z z').1 ≤ K := by
  have hp := pair_shape A s (z,z') r B K h
  constructor
  · have hl := h.left z q.1; have hr := h.right z' q.2
    simp only [term,StoredArrayEquality.conj,nodes,rename_nodes]; omega
  · apply StoredRunTable.conj_arity_le
    · rw [rename_arity]; exact h.left_arity z q.1
    · apply StoredRunTable.conj_arity_le
      · rw [rename_arity]; exact h.right_arity z' q.2
      · exact hp.2

def build (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (seed last : P) (first : Bool) : Data R (Params P s) 0 × Nat :=
  let a := parameter A s seed last first
  let b := StoredRunTable.any n (fun z => StoredRunTable.any n (term A s q r z))
  (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem value (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (seed last : P) (first : Bool) :
    denote (build A s q r seed last first).1 = A.original.switchGuard s q r seed last first := by
  simp only [build,StoredArrayEquality.conj,denote,parameter_value,StoredRunTable.any_value,term_value,
    SymbolicGuardedBlocks.Row.switchGuard]
  rfl
def budget (n B K : Nat) := 7+parameterBudget B K+StoredRunTable.anyBudget n (StoredRunTable.anyBudget n (termBudget n B K))
theorem bound (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (seed last : P) (first : Bool) (B K : Nat) (h : Bounds A B K) :
    (build A s q r seed last first).2 ≤ budget n B K := by
  have ha := parameter_bound A s seed last first B K h
  have hb := StoredRunTable.any_bound n (fun z => StoredRunTable.any n (term A s q r z)) _
    (fun z => StoredRunTable.any_bound n (term A s q r z) _ (fun z' => term_bound A s q r z z' B K h))
  simp only [build,budget]; omega

theorem any_nodes_bound (m : Nat) (f : Fin m → Data R P 0 × Nat) (B : Nat) (h : ∀ i, nodes (f i).1 ≤ B) :
    nodes (StoredRunTable.any m f).1 ≤ 1+m*(3+B) := by
  rw [← denote_nodes,StoredRunTable.any_value]
  apply ExactGuardedRunSize.nodes_any_le
  intro i
  rw [denote_nodes]
  exact h i
def sizeBudget (n B : Nat) := 6+B+n*(4+n*(24+4*B))
theorem shape (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (seed last : P) (first : Bool) (B K : Nat) (h : Bounds A B K) :
    nodes (build A s q r seed last first).1 ≤ sizeBudget n B ∧ arity (build A s q r seed last first).1 ≤ K := by
  have hp := parameter_shape A s seed last first B K h
  have ht (z z' : Fin n) := term_shape A s q r z z' B K h
  have hn := any_nodes_bound n (fun z => StoredRunTable.any n (term A s q r z)) _
    (fun z => any_nodes_bound n (term A s q r z) (21+4*B) (fun z' => (ht z z').1))
  constructor
  · simp only [build,StoredArrayEquality.conj,nodes,sizeBudget]
    nlinarith
  · apply StoredRunTable.conj_arity_le _ _ K hp.2
    apply StoredRunTable.any_arity_le
    intro z
    apply StoredRunTable.any_arity_le
    intro z'
    exact (ht z z').2

theorem qfree (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (seed last : P) (first : Bool) :
    (denote (build A s q r seed last first).1).IsQF := by
  rw [value]
  exact ExactGuardedRunFormula.switchGuard_qf A.original A.qfree.toRowQF s q r seed last first
theorem budget_diagonal (u : Nat) : budget u u u = 54+19*u+86*u^2+29*u^3+12*u^4 := by
  unfold budget parameterBudget termBudget pairBudget backBudget StoredRunTable.anyBudget
    StoredForwardTableBuild.tabBudget weight
  ring
theorem budget_polynomial (n B K : Nat) : budget n B K ≤ 200*(n+B+K+1)^4 := by
  let u := n+B+K+1
  have hn : n ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hm : budget n B K ≤ budget u u u := by
    unfold budget parameterBudget termBudget pairBudget backBudget StoredRunTable.anyBudget
      StoredForwardTableBuild.tabBudget weight
    gcongr
  have hp (j : Nat) : u^j ≤ u^(j+1) := by
    simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right (u^j) hu
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  norm_num at h0 h1 h2 h3
  rw [budget_diagonal] at hm
  change budget n B K ≤ 200*u^4
  linarith only [hm,h0,h1,h2,h3]
theorem polynomial (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (seed last : P) (first : Bool) (B K : Nat) (h : Bounds A B K) :
    (build A s q r seed last first).2 ≤ 200*(n+B+K+1)^4 :=
  (bound A s q r seed last first B K h).trans (budget_polynomial n B K)
end NSSE.StoredRawSwitchGuard
