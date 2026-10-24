import NSSE.StoredGuardedArrayRun

/-! Output size and relation arity of actual guarded array compilation. -/
namespace NSSE.StoredGuardedArrayShape
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n q T : Nat}

theorem matrix_arity {k : Nat} (a : Data R (P ⊕ Fin k) 0) (h : (denote a).IsQF) :
    arity (StoredRelationalClosure.matrix a h).1 = arity a := by
  cases a with
  | falsum => simp only [StoredRelationalClosure.matrix,arity]
  | equal x y => simp only [StoredRelationalClosure.matrix,arity]
  | rel r args => simp only [StoredRelationalClosure.matrix,arity]
  | imp a b => simp only [StoredRelationalClosure.matrix,arity,matrix_arity a,matrix_arity b]
  | all a => exact False.elim (BoundedFormula.not_all_isQF (denote a) h)
theorem prefix_arity {k : Nat} (a : Data R P k) :
    arity (StoredRelationalClosure.bindAll a).1 = arity a := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [StoredRelationalClosure.bindAll,ih,arity,Nat.max_zero]
theorem closure_arity (a : StoredRelationalClosure.Package R P) :
    arity (StoredRelationalClosure.build a).1 = arity a.body := by
  simp only [StoredRelationalClosure.build,StoredRelationalClosure.close,prefix_arity,matrix_arity]

theorem dynamic_shape (A : StoredDynamicColumn.Automaton R P n) (C : StoredDynamicRun.Columns P)
    (one : P) (positive : Bool) (c d B K : Nat) (h : StoredDynamicColumn.Bounds A c B K)
    (hc : ∀ t < T, (C t).2 ≤ d) :
    nodes (StoredDynamicRun.closed A C one T positive).1 ≤
      StoredRunTable.sizeBudget n T (StoredDynamicRun.labelSize B) ∧
    arity (StoredDynamicRun.closed A C one T positive).1 ≤ K := by
  have hl := StoredDynamicRun.label_bounds A C one c d B K h hc
  constructor
  · exact StoredRunTable.closed_nodes _ _ _ one positive _ _ _ hl
  · simp only [StoredDynamicRun.closed,StoredRunTable.closed,closure_arity]
    exact StoredRunTable.package_arity _ _ _ one positive _ _ _ hl

def sizeBudget (n T B : Nat) := StoredRunTable.sizeBudget (2*n*n) T
  (StoredDynamicRun.labelSize (StoredRawSkippedRun.nodeBudget n B))
theorem raw_shape (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (C : StoredDynamicRun.Columns P) (one : P) (positive : Bool) (d B K : Nat)
    (h : StoredRawBackGuards.Bounds A B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    nodes (StoredRawSkippedRun.closed A e seed last first C one T positive).1 ≤ sizeBudget n T B ∧
    arity (StoredRawSkippedRun.closed A e seed last first C one T positive).1 ≤ K := by
  have hs := dynamic_shape (StoredRawSkippedRun.build A e seed last first).1.automaton C one positive
    (StoredRawSkippedRun.costBudget n B K) d (StoredRawSkippedRun.nodeBudget n B) K
    (StoredRawSkippedRun.bounds A e seed last first B K h) hc
  have hn := StoredRawStates.count_value (StoredRawSkippedRun.build A e seed last first).1.table
  simp only [hn] at hs
  exact hs

theorem shape (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) (B K : Nat)
    (h : StoredRowTransport.Bounds A B K) :
    nodes (StoredGuardedArrayRun.closed A e seed last first zero one args T positive).1 ≤ sizeBudget n T B ∧
    arity (StoredGuardedArrayRun.closed A e seed last first zero one args T positive).1 ≤ K := by
  exact raw_shape (T := T) (StoredRowTransport.build StoredGuardedArrayRun.liftName A).1 e (.inl seed) (.inl last) first
    (StoredArrayColumns.build zero args T) (.inl one) positive (StoredArrayColumns.budget q T) B K
    (StoredRowTransport.preserves StoredGuardedArrayRun.liftName A B K h).toBounds
    (fun t _ => StoredArrayColumns.bound zero args t)

theorem size_diagonal (u : Nat) : sizeBudget u u u =
    19+8*u+1982*u^2+378*u^3+576*u^4+2736*u^5+448*u^6+768*u^7+128*u^8 := by
  unfold sizeBudget StoredRunTable.sizeBudget StoredDynamicRun.labelSize StoredRawSkippedRun.nodeBudget
    StoredRawAutomaton.nodeBudget StoredRawTransition.sizeBudget StoredRawSwitchGuard.sizeBudget
  ring

theorem size_polynomial (n T B : Nat) : sizeBudget n T B ≤ 7043*(n+T+B+1)^8 := by
  let u := n+T+B+1
  have hn : n ≤ u := by dsimp [u]; omega
  have ht : T ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hm : sizeBudget n T B ≤ sizeBudget u u u := by
    unfold sizeBudget StoredRunTable.sizeBudget StoredDynamicRun.labelSize StoredRawSkippedRun.nodeBudget
      StoredRawAutomaton.nodeBudget StoredRawTransition.sizeBudget StoredRawSwitchGuard.sizeBudget
    gcongr
  have hp (j : Nat) : u^j ≤ u^(j+1) := by
    simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right (u^j) hu
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
  have h4 := hp 4; have h5 := hp 5; have h6 := hp 6; have h7 := hp 7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  rw [size_diagonal] at hm
  change sizeBudget n T B ≤ 7043*u^8
  linarith only [hm,h0,h1,h2,h3,h4,h5,h6,h7]
end NSSE.StoredGuardedArrayShape
