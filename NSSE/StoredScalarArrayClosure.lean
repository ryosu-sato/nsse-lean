import NSSE.StoredScalarValidityJoin

/-! Measured array-coordinate count and actual outer existential closure. -/
namespace NSSE.StoredScalarArrayClosure
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {k c q T : Nat} {ns : Fin k → Nat}

def coordinateCount (q T : Nat) : Nat × Nat :=
  let a := CountedSupportRule.add T 1
  let b := CountedSupportRule.mul a.1 q
  let d := CountedSupportRule.add b.1 b.1
  (d.1,3+a.2+b.2+d.2)
theorem count_value (q T : Nat) : (coordinateCount q T).1 = count q T := by
  simp only [coordinateCount,CountedSupportRule.add_value,CountedSupportRule.mul_value,count,slots]
def countBudget (q T : Nat) := 6+T+q*(T+3)+(T+1)*q
theorem count_bound (q T : Nat) : (coordinateCount q T).2 ≤ countBudget q T := by
  simp only [coordinateCount,CountedSupportRule.add_cost,CountedSupportRule.mul_cost,
    CountedSupportRule.add_value,CountedSupportRule.mul_value,countBudget]
  ring_nf
  omega

def bindMeasured {m : Nat} (d : Nat × Nat) (h : d.1=m) (A : StoredRelationalClosure.Package R (P ⊕ Fin m)) :=
  StoredRelationalPackages.bind d.1 (cast (congrArg (fun j => StoredRelationalClosure.Package R (P ⊕ Fin j)) h.symm) A)
theorem bind_eq {m : Nat} (d : Nat × Nat) (h : d.1=m) (A : StoredRelationalClosure.Package R (P ⊕ Fin m)) :
    bindMeasured d h A = StoredRelationalPackages.bind m A := by
  subst m; rfl

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (T : Nat) (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool) :=
  let a := StoredScalarValidityJoin.build rows C seed last zero one T φ h positive
  let d := coordinateCount q T
  let b := bindMeasured d (count_value q T) a.1
  let f := StoredRelationalClosure.build b.1
  (f.1,3+a.2+d.2+b.2+f.2)

def sizeBudget (ns : Fin k → Nat) (c q T B N : Nat) :=
  StoredScalarValidityJoin.sizeBudget ns c q T B N+5*count q T
def budget (ns : Fin k → Nat) (c q T B K N : Nat) :=
  let S := StoredScalarValidityJoin.sizeBudget ns c q T B N
  let m := count q T
  7+StoredScalarValidityJoin.budget ns c q T B K N+countBudget q T+m+
    weight K (m+4)*S+(5+3*K)*S+6*(m+S)

theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    nodes (build rows C seed last zero one T φ h positive).1 ≤ sizeBudget ns c q T B (nodes φ) ∧
    arity (build rows C seed last zero one T φ h positive).1 ≤ K := by
  have ha := StoredScalarValidityJoin.shape (T := T) rows C seed last zero one φ h positive B K hr hc
  have hb := StoredRelationalPackages.bind_shape (count q T) (StoredScalarValidityJoin.build rows C seed last zero one T φ h positive).1
  constructor
  · simp only [build,bind_eq,StoredRelationalClosure.build_nodes,sizeBudget]
    have := ha.1
    simp only [StoredRelationalElimination.size] at this
    rw [hb.2.1]
    have := hb.1
    omega
  · simp only [build,bind_eq,StoredGuardedArrayShape.closure_arity,hb.2.2]
    exact ha.2

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last zero one T φ h positive).2 ≤ budget ns c q T B K (nodes φ) := by
  let a := (StoredScalarValidityJoin.build rows C seed last zero one T φ h positive).1
  have ha := StoredScalarValidityJoin.shape (T := T) rows C seed last zero one φ h positive B K hr hc
  have ca := StoredScalarValidityJoin.bound (T := T) rows C seed last zero one φ h positive B K hr hc
  have cd := count_bound q T
  have cb := StoredRelationalPackages.bind_bound (count q T) a K ha.2
  have hb := StoredRelationalPackages.bind_shape (count q T) a
  have cf := StoredRelationalClosure.build_bound (StoredRelationalPackages.bind (count q T) a).1 K (by rw [hb.2.2]; exact ha.2)
  let S := StoredScalarValidityJoin.sizeBudget ns c q T B (nodes φ)
  have hn : nodes a.body ≤ S := by have := ha.1; change nodes a.body+5*a.vars ≤ S at this; omega
  have hv : a.vars ≤ S := by have := ha.1; change nodes a.body+5*a.vars ≤ S at this; omega
  have hm := Nat.mul_le_mul_left (weight K (count q T+4)) hn
  have hf := Nat.mul_le_mul_left (5+3*K) hn
  rw [hb.2.1] at cf
  simp only [build,bind_eq,budget]
  dsimp only [S,a] at hn hv hm hf cb cf hb
  omega

theorem correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nonempty D] (p : P → D) :
    Formula.Realize (denote (build rows C seed last zero one T φ h positive).1) p ↔
      Formula.Realize (SymbolicReachability.closeColumn (FiniteWordArrayRepresentation.valid zero one q T ⊓
        BoundedExistentialScalarLowering.matrix rows.original C.original seed last zero one T (denote φ) positive)) p := by
  simp only [build,bind_eq,StoredRelationalClosure.build_value,StoredRelationalPackages.bind_original,
    ExistentialFormulaPackage.Package.bind_correct,SymbolicReachability.realize_closeColumn,StoredScalarValidityJoin.correct]
end NSSE.StoredScalarArrayClosure
