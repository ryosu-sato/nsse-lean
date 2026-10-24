import NSSE.StoredGuardedArrayShape

/-! Actual existential package of the original guarded array compiler. -/
namespace NSSE.StoredGuardedArrayPackage
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {n q T : Nat}

def build (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (T : Nat) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := StoredRowTransport.build StoredGuardedArrayRun.liftName A
  let b := StoredRawSkippedRun.build a.1 e (.inl seed) (.inl last) first
  let f := StoredDynamicRun.package b.1.automaton (StoredArrayColumns.build zero args T) (.inl one) T positive
  (f.1,2+a.2+b.2+f.2)

theorem value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) :
    (build A e seed last first zero one args T positive).1.original.toFormula =
      FiniteArrayHFormula.compile A.original e seed last first zero one q T
        (fun i => (StoredRelationTuple.read args i).1) positive := by
  rw [← StoredGuardedArrayRun.original_value]
  simp only [build,StoredDynamicRun.package_value,StoredGuardedArrayRun.closed,StoredRawSkippedRun.closed,
    StoredDynamicRun.closed_value]

def labelCost (n q T B K : Nat) := StoredDynamicRun.labelCost (StoredRawSkippedRun.costBudget n B K)
  (StoredArrayColumns.budget q T) (StoredRawSkippedRun.nodeBudget n B) K
def labelSize (n B : Nat) := StoredDynamicRun.labelSize (StoredRawSkippedRun.nodeBudget n B)
def budget (n q T B K : Nat) := 4+StoredRowTransport.budget n 1 B K+StoredRawStates.budget n+
  StoredRunTable.budget (2*n*n) T (labelCost n q T B K) (labelSize n B) K

theorem bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) (B K : Nat)
    (h : StoredRowTransport.Bounds A B K) :
    (build A e seed last first zero one args T positive).2 ≤ budget n q T B K := by
  let a := (StoredRowTransport.build (StoredGuardedArrayRun.liftName (q := q) (T := T)) A).1
  let b := (StoredRawSkippedRun.build a e (.inl seed) (.inl last) first).1
  have ha := StoredRowTransport.bound (StoredGuardedArrayRun.liftName (q := q) (T := T)) A 1 B K (fun _ => le_rfl) h
  have hb := StoredRawSkippedRun.build_bound a e (.inl seed) (.inl last) first
  have hs := StoredRawSkippedRun.bounds a e (.inl seed) (.inl last) first B K
    (StoredRowTransport.preserves StoredGuardedArrayRun.liftName A B K h).toBounds
  have hf := StoredDynamicRun.package_bound (T := T) b.automaton (StoredArrayColumns.build zero args T) (.inl one) positive
    (StoredRawSkippedRun.costBudget n B K) (StoredArrayColumns.budget q T) (StoredRawSkippedRun.nodeBudget n B) K hs
    (fun t _ => StoredArrayColumns.bound zero args t)
  have hn := StoredRawStates.count_value b.table
  simp only [hn] at hf
  dsimp only [b,a] at hb hf
  change 2+_+_+_ ≤ _
  unfold budget labelCost labelSize
  omega

theorem shape (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) (B K : Nat)
    (h : StoredRowTransport.Bounds A B K) :
    StoredRelationalElimination.size (build A e seed last first zero one args T positive).1 ≤
      StoredGuardedArrayShape.sizeBudget n T B ∧
    arity (build A e seed last first zero one args T positive).1.body ≤ K := by
  let a := (StoredRowTransport.build (StoredGuardedArrayRun.liftName (q := q) (T := T)) A).1
  let b := (StoredRawSkippedRun.build a e (.inl seed) (.inl last) first).1
  have hs := StoredDynamicRun.package_shape (T := T) b.automaton (StoredArrayColumns.build zero args T) (.inl one) positive
    (StoredRawSkippedRun.costBudget n B K) (StoredArrayColumns.budget q T) (StoredRawSkippedRun.nodeBudget n B) K
    (StoredRawSkippedRun.bounds a e (.inl seed) (.inl last) first B K
      (StoredRowTransport.preserves StoredGuardedArrayRun.liftName A B K h).toBounds)
    (fun t _ => StoredArrayColumns.bound zero args t)
  have hn := StoredRawStates.count_value b.table
  simp only [hn] at hs
  exact hs

theorem vars (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) :
    (build A e seed last first zero one args T positive).1.vars = (T+1)*(2*n*n) := by
  simp only [build,StoredDynamicRun.package,StoredRunTable.package_vars,StoredRawStates.count_value]
end NSSE.StoredGuardedArrayPackage
