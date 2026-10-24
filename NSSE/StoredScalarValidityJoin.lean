import NSSE.StoredArraySignedLowering

/-! Actual validity conjunction with signed scalar array matrix packages. -/
namespace NSSE.StoredScalarValidityJoin
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {k c q T : Nat} {ns : Fin k → Nat}

def validSize (q T : Nat) := 3+T*(8+8*q)
theorem validity_shape (zero one : P) :
    StoredRelationalElimination.size (StoredArrayValidity.package (R := R) zero one q T).1 = validSize q T ∧
    arity (StoredArrayValidity.package (R := R) zero one q T).1.body = 0 := by
  have ha := StoredRelationalPackages.atom_shape (StoredArrayValidity.build (R := R) one q T).1
    (StoredArrayValidity.qfree zero one)
  have hn := StoredArrayValidity.nodes_value (R := R) (q := q) (T := T) zero one
  have hk := StoredArrayValidity.arity_value (R := R) (q := q) (T := T) one
  simp only [StoredArrayValidity.package,StoredRelationalElimination.size,validSize]
  omega

def build (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (T : Nat) (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool) :=
  let v := StoredArrayValidity.package zero one q T
  let a := StoredArraySignedLowering.build rows C seed last zero one T φ h positive
  let b := StoredRelationalPackages.conj v.1 a.1
  (b.1,3+v.2+a.2+b.2)
def sizeBudget (ns : Fin k → Nat) (c q T B N : Nat) :=
  5+validSize q T+(StoredArraySignedAtoms.sizeBudget ns c T B+5)*N
def budget (ns : Fin k → Nat) (c q T B K N : Nat) :=
  5+StoredArrayValidity.budget q T+5*validSize q T+
  (StoredArraySignedAtoms.costBudget ns c q T B K+4+
    StoredRelationalElimination.joinBudget ((StoredArraySignedAtoms.sizeBudget ns c T B+5)*N) K)*N+
  StoredRelationalElimination.joinBudget (sizeBudget ns c q T B N) K

theorem shape (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    StoredRelationalElimination.size (build rows C seed last zero one T φ h positive).1 ≤ sizeBudget ns c q T B (nodes φ) ∧
    arity (build rows C seed last zero one T φ h positive).1.body ≤ K := by
  have hv := validity_shape (R := R) (q := q) (T := T) zero one
  have ha := StoredArraySignedLowering.shape (T := T) rows C seed last zero one φ h positive B K hr hc
  have hj := StoredRelationalPackages.conj_shape (StoredArrayValidity.package (R := R) zero one q T).1
    (StoredArraySignedLowering.build rows C seed last zero one T φ h positive).1
  constructor
  · simp only [StoredRelationalElimination.size] at hv ha ⊢
    simp only [build,sizeBudget]
    rw [hj.2.1]
    have hn := hj.1
    omega
  · change arity (StoredRelationalPackages.conj _ _).1.body ≤ K
    rw [hj.2.2,hv.2]
    exact max_le (Nat.zero_le _) ha.2

theorem bound (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last zero one T φ h positive).2 ≤ budget ns c q T B K (nodes φ) := by
  have hv := validity_shape (R := R) (q := q) (T := T) zero one
  have ha := StoredArraySignedLowering.shape (T := T) rows C seed last zero one φ h positive B K hr hc
  have cv := StoredArrayValidity.package_bound (R := R) (q := q) (T := T) zero one
  have ca := StoredArraySignedLowering.bound (T := T) rows C seed last zero one φ h positive B K hr hc
  have hj := StoredRelationalElimination.conj_bound (StoredArrayValidity.package (R := R) zero one q T).1
    (StoredArraySignedLowering.build rows C seed last zero one T φ h positive).1
    (sizeBudget ns c q T B (nodes φ)) K
    (by rw [hv.1]; unfold sizeBudget; omega) (by unfold sizeBudget; omega)
    (by rw [hv.2]; omega) ha.2
  simp only [build,budget,validSize] at *
  omega

theorem correct (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (φ : Data (UnifiedBlockPresentation.Rel ns c) Empty q) (h : (denote φ).IsQF) (positive : Bool)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [Nonempty D] (p : Params P q T → D) :
    Formula.Realize (build rows C seed last zero one T φ h positive).1.original.toFormula p ↔
      Formula.Realize (FiniteWordArrayRepresentation.valid zero one q T ⊓
        BoundedExistentialScalarLowering.matrix rows.original C.original seed last zero one T (denote φ) positive) p := by
  simp only [build,StoredRelationalPackages.conj_original,ExistentialFormulaPackage.Package.conj_correct,
    StoredArrayValidity.package_value,ExistentialFormulaPackage.Package.atom_correct,
    StoredArraySignedLowering.correct,Formula.realize_inf]
end NSSE.StoredScalarValidityJoin
